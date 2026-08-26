/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.RectangleGeometryCore
import GluelumpPerimeterLaw.Propagation.StraightLine

/-!
# Canonical rectangle expectations in a neutral reflection-positive state

This file turns the pointwise coordinate-cap geometry into the exact analytic
rectangle package used by perimeter extrapolation.  Integer cuts are discharged
by `Gauge.ReflectionPositiveState`.  Half-integer cuts are isolated behind the
small `CanonicalRectangleLinkReflectionData` interface, since completed-box
gauge fixing is the construction that supplies them in the intended model.

No strong-coupling construction or thermodynamic-limit theorem is imported.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

variable (rho : ContinuousUnitaryRepData G n)
  {a b : Fin d} (hab : a ≠ b)

/-- The complex expectation of the parity-adapted reflected representative of
an `R × T` rectangle. -/
def canonicalRectangleIntegral
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) : ℂ :=
  ∫ A, rho.wilsonLoop (reflectedRectangleLoop hab R T) A
    ∂(mu : Measure (Configuration d G))

/-- The corresponding real-valued rectangle expectation.  Reality is proved
below, rather than built into this definition. -/
def canonicalRectangleExpectation
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) : ℝ :=
  (canonicalRectangleIntegral mu rho hab R T).re

/-- The origin-based standard rectangle integral used for translation and
axis-swap transport. -/
def rectangleBoundaryIntegral
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (a b : Fin d) (R T : ℕ) : ℂ :=
  ∫ A, rho.wilsonLoop (Path.rectangleBoundary 0 a b R T) A
    ∂(mu : Measure (Configuration d G))

/-- The precise gauge-fixed half-integer-cut input needed by the rectangle
argument.  It asks only for positivity of balanced closures and
Cauchy--Schwarz for mixed coordinate caps. -/
structure CanonicalRectangleLinkReflectionData
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) : Prop where
  positive : ∀ r T,
    (∫ A, rho.wilsonLoop (linkClosedCoordinateCaps hab r r T) A
      ∂(mu : Measure (Configuration d G))).im = 0 ∧
    0 ≤ (∫ A, rho.wilsonLoop (linkClosedCoordinateCaps hab r r T) A
      ∂(mu : Measure (Configuration d G))).re
  cauchySchwarz : ∀ r s T,
    Complex.normSq (∫ A,
      rho.wilsonLoop (linkClosedCoordinateCaps hab r s T) A
        ∂(mu : Measure (Configuration d G))) ≤
      (∫ A, rho.wilsonLoop (linkClosedCoordinateCaps hab r r T) A
        ∂(mu : Measure (Configuration d G))).re *
      (∫ A, rho.wilsonLoop (linkClosedCoordinateCaps hab s s T) A
        ∂(mu : Measure (Configuration d G))).re

/-- Integral invariance under every transposition of coordinate labels.  The
completed free-boundary limit supplies this through diagonal-reflection
invariance of the limiting state. -/
def RectangleAxisSwapInvariant
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n) : Prop :=
  ∀ {tau sigma : Fin d}, tau ≠ sigma → ∀ a b R T,
    rectangleBoundaryIntegral mu rho (Equiv.swap tau sigma a)
        (Equiv.swap tau sigma b) R T =
      rectangleBoundaryIntegral mu rho a b R T

/-- Cyclic recutting and translation invariance identify the reflected
representative with the standard rectangle based at the origin. -/
theorem canonicalRectangleIntegral_eq_rectangleBoundaryIntegral
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    canonicalRectangleIntegral mu rho hab R T =
      rectangleBoundaryIntegral mu rho a b R T := by
  unfold canonicalRectangleIntegral rectangleBoundaryIntegral
  calc
    (∫ A, rho.wilsonLoop (reflectedRectangleLoop hab R T) A
        ∂(mu : Measure (Configuration d G))) =
        ∫ A, rho.wilsonLoop
          (Path.rectangleBoundary (rectangleCutBase a b R T) a b R T) A
            ∂(mu : Measure (Configuration d G)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        wilsonLoop_reflectedRectangleLoop_eq_rectangleBoundary
          rho hab R T A
    _ = ∫ A, rho.wilsonLoop (Path.rectangleBoundary 0 a b R T) A
          ∂(mu : Measure (Configuration d G)) := by
      have htranslate := hstate.localExpectation_translatePullback
        (rectangleCutBase a b R T)
        (rho.wilsonLoop (Path.rectangleBoundary 0 a b R T))
      simpa only [LocalObservable.translatePullback_apply,
        wilsonLoop_rectangleBoundary_translate] using htranslate

/-- Site/link reflection positivity makes the complex rectangle integral
literally real. -/
theorem canonicalRectangleIntegral_im_eq_zero
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (R T : ℕ) :
    (canonicalRectangleIntegral mu rho hab R T).im = 0 := by
  rcases Nat.even_or_odd' R with ⟨r, rfl | rfl⟩
  · have hx : siteReflection a 0 (0 : Site d) = 0 := by
      ext i
      by_cases hi : i = a
      · subst i
        simp
      · rw [siteReflection_apply_ne hi]
    have hpos :=
      YangMills.Gluelump.Propagation.ReflectionPositiveState.siteCapsPositive
        hstate rho a 0
      (siteCoordinateCap a b r T) hx
      (siteReflection_axisPoint_other_fixed hab T)
      (siteCoordinateCap_sitePositive hab r T)
    simpa only [canonicalRectangleIntegral, reflectedRectangleLoop_even,
      siteClosedCoordinateCaps] using hpos.1
  · simpa only [canonicalRectangleIntegral, reflectedRectangleLoop_odd]
      using (hlink.positive r T).1

/-- The real rectangle expectation is nonnegative at every pair of side
lengths. -/
theorem canonicalRectangleExpectation_nonneg
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (R T : ℕ) :
    0 ≤ canonicalRectangleExpectation mu rho hab R T := by
  rcases Nat.even_or_odd' R with ⟨r, rfl | rfl⟩
  · have hx : siteReflection a 0 (0 : Site d) = 0 := by
      ext i
      by_cases hi : i = a
      · subst i
        simp
      · rw [siteReflection_apply_ne hi]
    have hpos :=
      YangMills.Gluelump.Propagation.ReflectionPositiveState.siteCapsPositive
        hstate rho a 0
      (siteCoordinateCap a b r T) hx
      (siteReflection_axisPoint_other_fixed hab T)
      (siteCoordinateCap_sitePositive hab r T)
    simpa only [canonicalRectangleExpectation, canonicalRectangleIntegral,
      reflectedRectangleLoop_even, siteClosedCoordinateCaps] using hpos.2
  · simpa only [canonicalRectangleExpectation, canonicalRectangleIntegral,
      reflectedRectangleLoop_odd] using (hlink.positive r T).2

/-- Character normalization and probability normalization bound every
rectangle expectation by one. -/
theorem canonicalRectangleExpectation_le_one
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    canonicalRectangleExpectation mu rho hab R T ≤ 1 := by
  unfold canonicalRectangleExpectation canonicalRectangleIntegral
  calc
    (∫ A, rho.wilsonLoop (reflectedRectangleLoop hab R T) A
        ∂(mu : Measure (Configuration d G))).re ≤
        ‖∫ A, rho.wilsonLoop (reflectedRectangleLoop hab R T) A
          ∂(mu : Measure (Configuration d G))‖ :=
      Complex.re_le_norm _
    _ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (mu : Measure (Configuration d G))) (C := (1 : ℝ)) <|
          ae_of_all _ fun A =>
            rho.norm_wilsonLoop_le_one (reflectedRectangleLoop hab R T) A

/-- Reflection Cauchy--Schwarz gives adjacent log-convexity in the first side
length.  Even midpoints use a site plane and odd midpoints use the link-cut
callback. -/
theorem canonicalRectangleExpectation_width_reflectionLogConvex
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (T : ℕ) :
    ReflectionLogConvex
      (fun R => canonicalRectangleExpectation mu rho hab R T) := by
  intro m
  rcases Nat.even_or_odd' m with ⟨r, rfl | rfl⟩
  · have hx : siteReflection a 0 (0 : Site d) = 0 := by
      ext i
      by_cases hi : i = a
      · subst i
        simp
      · rw [siteReflection_apply_ne hi]
    have hcs :=
      YangMills.Gluelump.Propagation.ReflectionPositiveState.siteCapsCauchySchwarz
        hstate rho a 0
      (siteCoordinateCap a b r T)
      (siteCoordinateCap a b (r + 1) T)
      hx (siteReflection_axisPoint_other_fixed hab T)
      (siteCoordinateCap_sitePositive hab r T)
      (siteCoordinateCap_sitePositive hab (r + 1) T)
    have hreSq :
        (Complex.re (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r (r + 1) T) A
          ∂(mu : Measure (Configuration d G)))) ^ 2 ≤
        Complex.normSq (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r (r + 1) T) A
          ∂(mu : Measure (Configuration d G))) := by
      simpa [pow_two] using Complex.re_sq_le_normSq
        (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r (r + 1) T) A
          ∂(mu : Measure (Configuration d G)))
    have hcs' :
        Complex.normSq (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r (r + 1) T) A
          ∂(mu : Measure (Configuration d G))) ≤
        Complex.re (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r r T) A
          ∂(mu : Measure (Configuration d G))) *
        Complex.re (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab (r + 1) (r + 1) T) A
          ∂(mu : Measure (Configuration d G))) := by
      simpa only [siteClosedCoordinateCaps] using hcs
    calc
      canonicalRectangleExpectation mu rho hab (2 * r + 1) T ^ 2 =
          (Complex.re (∫ A, rho.wilsonLoop
            (siteClosedCoordinateCaps hab r (r + 1) T) A
            ∂(mu : Measure (Configuration d G)))) ^ 2 := by
        rw [canonicalRectangleExpectation, canonicalRectangleIntegral,
          siteClosedCoordinateCaps_eq_reflectedRectangleLoop_odd]
      _ ≤ Complex.normSq (∫ A, rho.wilsonLoop
          (siteClosedCoordinateCaps hab r (r + 1) T) A
          ∂(mu : Measure (Configuration d G))) := hreSq
      _ ≤ _ := hcs'
      _ = canonicalRectangleExpectation mu rho hab (2 * r) T *
          canonicalRectangleExpectation mu rho hab (2 * r + 2) T := by
        rw [show 2 * r + 2 = 2 * (r + 1) by omega]
        simp only [canonicalRectangleExpectation, canonicalRectangleIntegral,
          reflectedRectangleLoop_even]
  · have hcs := hlink.cauchySchwarz (r + 1) r T
    have hreSq :
        (Complex.re (∫ A, rho.wilsonLoop
          (linkClosedCoordinateCaps hab (r + 1) r T) A
          ∂(mu : Measure (Configuration d G)))) ^ 2 ≤
        Complex.normSq (∫ A, rho.wilsonLoop
          (linkClosedCoordinateCaps hab (r + 1) r T) A
          ∂(mu : Measure (Configuration d G))) := by
      simpa [pow_two] using Complex.re_sq_le_normSq
        (∫ A, rho.wilsonLoop
          (linkClosedCoordinateCaps hab (r + 1) r T) A
          ∂(mu : Measure (Configuration d G)))
    calc
      canonicalRectangleExpectation mu rho hab (2 * r + 1 + 1) T ^ 2 =
          (Complex.re (∫ A, rho.wilsonLoop
            (linkClosedCoordinateCaps hab (r + 1) r T) A
            ∂(mu : Measure (Configuration d G)))) ^ 2 := by
        rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega,
          canonicalRectangleExpectation, canonicalRectangleIntegral,
          ← linkClosedCoordinateCaps_succ_eq_reflectedRectangleLoop_even]
      _ ≤ Complex.normSq (∫ A, rho.wilsonLoop
          (linkClosedCoordinateCaps hab (r + 1) r T) A
          ∂(mu : Measure (Configuration d G))) := hreSq
      _ ≤ _ := hcs
      _ = canonicalRectangleExpectation mu rho hab (2 * r + 1) T *
          canonicalRectangleExpectation mu rho hab (2 * r + 1 + 2) T := by
        rw [show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by omega]
        simp only [canonicalRectangleExpectation, canonicalRectangleIntegral,
          reflectedRectangleLoop_odd]
        rw [mul_comm]

/-- Reality transfers from the reflected representative to the origin-based
standard rectangle. -/
theorem rectangleBoundaryIntegral_im_eq_zero
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (R T : ℕ) :
    (rectangleBoundaryIntegral mu rho a b R T).im = 0 := by
  rw [← canonicalRectangleIntegral_eq_rectangleBoundaryIntegral
    hstate rho hab R T]
  exact canonicalRectangleIntegral_im_eq_zero
    (mu := mu) (rho := rho) (hab := hab) hstate hlink R T

/-- Axis-swap invariance plus orientation reversal gives literal complex
transpose symmetry; the last conjugation disappears by the reality theorem. -/
theorem canonicalRectangleIntegral_transpose
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (hswap : RectangleAxisSwapInvariant mu rho)
    (R T : ℕ) :
    canonicalRectangleIntegral mu rho hab R T =
      canonicalRectangleIntegral mu rho hab T R := by
  have hswap' :
      rectangleBoundaryIntegral mu rho b a T R =
        rectangleBoundaryIntegral mu rho a b T R := by
    simpa [RectangleAxisSwapInvariant, hab] using
      hswap hab a b T R
  have hreverse :
      rectangleBoundaryIntegral mu rho b a T R =
        star (rectangleBoundaryIntegral mu rho a b R T) := by
    unfold rectangleBoundaryIntegral
    rw [rectangleBoundary_swap_axes_eq_reverse hab R T]
    calc
      (∫ A, rho.wilsonLoop
          (Path.rectangleBoundary 0 a b R T).reverse A
          ∂(mu : Measure (Configuration d G))) =
          ∫ A, star (rho.wilsonLoop
            (Path.rectangleBoundary 0 a b R T) A)
            ∂(mu : Measure (Configuration d G)) := by
        apply integral_congr_ae
        exact ae_of_all _ fun A =>
          rho.wilsonLoop_reverse (Path.rectangleBoundary 0 a b R T) A
      _ = _ := integral_conj
  have hconj :
      rectangleBoundaryIntegral mu rho a b T R =
        star (rectangleBoundaryIntegral mu rho a b R T) :=
    hswap'.symm.trans hreverse
  have hreal := rectangleBoundaryIntegral_im_eq_zero
    (mu := mu) (rho := rho) (hab := hab) hstate hlink R T
  have hstar :
      star (rectangleBoundaryIntegral mu rho a b R T) =
        rectangleBoundaryIntegral mu rho a b R T := by
    apply Complex.ext
    · simp
    · simp [hreal]
  rw [canonicalRectangleIntegral_eq_rectangleBoundaryIntegral
      hstate rho hab R T,
    canonicalRectangleIntegral_eq_rectangleBoundaryIntegral
      hstate rho hab T R]
  exact (hconj.trans hstar).symm

/-- Transpose symmetry for the real-valued expectation. -/
theorem canonicalRectangleExpectation_transpose
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (hswap : RectangleAxisSwapInvariant mu rho)
    (R T : ℕ) :
    canonicalRectangleExpectation mu rho hab R T =
      canonicalRectangleExpectation mu rho hab T R := by
  exact congrArg Complex.re
    (canonicalRectangleIntegral_transpose
      (mu := mu) (rho := rho) (hab := hab) hstate hlink hswap R T)

/-- The complete neutral rectangle package used by square-to-rectangle
perimeter extrapolation. -/
structure CanonicalRectangleExpectationCertificate
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) : Prop where
  reality : ∀ R T, (canonicalRectangleIntegral mu rho hab R T).im = 0
  nonnegative : ∀ R T,
    0 ≤ canonicalRectangleExpectation mu rho hab R T
  le_one : ∀ R T, canonicalRectangleExpectation mu rho hab R T ≤ 1
  width_logConvex : ∀ T,
    ReflectionLogConvex
      (fun R => canonicalRectangleExpectation mu rho hab R T)
  side_logConvex : ∀ R,
    ReflectionLogConvex (canonicalRectangleExpectation mu rho hab R)
  transpose : ∀ R T,
    canonicalRectangleExpectation mu rho hab R T =
      canonicalRectangleExpectation mu rho hab T R

/-- Site RP together with the two explicit callbacks produces the full
canonical rectangle certificate. -/
theorem canonicalRectangleExpectationCertificate
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (hlink : CanonicalRectangleLinkReflectionData mu rho hab)
    (hswap : RectangleAxisSwapInvariant mu rho) :
    CanonicalRectangleExpectationCertificate mu rho hab where
  reality := canonicalRectangleIntegral_im_eq_zero
    (mu := mu) (rho := rho) (hab := hab) hstate hlink
  nonnegative := canonicalRectangleExpectation_nonneg
    (mu := mu) (rho := rho) (hab := hab) hstate hlink
  le_one := canonicalRectangleExpectation_le_one mu rho hab
  width_logConvex :=
    canonicalRectangleExpectation_width_reflectionLogConvex
      (mu := mu) (rho := rho) (hab := hab) hstate hlink
  side_logConvex := fun R => by
    have hlog := canonicalRectangleExpectation_width_reflectionLogConvex
      (mu := mu) (rho := rho) (hab := hab) hstate hlink R
    intro T
    simpa only [canonicalRectangleExpectation_transpose
      (mu := mu) (rho := rho) (hab := hab) hstate hlink hswap] using hlog T
  transpose := canonicalRectangleExpectation_transpose
    (mu := mu) (rho := rho) (hab := hab) hstate hlink hswap

end

end YangMills.Gluelump.Propagation
