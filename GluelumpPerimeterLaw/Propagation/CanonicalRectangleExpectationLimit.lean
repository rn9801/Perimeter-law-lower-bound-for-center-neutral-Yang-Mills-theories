/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation
import GluelumpPerimeterLaw.Propagation.RectangleReflection
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryReflectionPositiveState

/-!
# Ordinary free-boundary adapter for canonical rectangle expectations

This is the thin model-specific discharge of the two callbacks in
`CanonicalRectangleExpectation`.  Gauge-fixed crossing families supply the
half-integer cuts, while coordinate-swap invariance of the free-boundary boxes
supplies axis transport.  The neutral rectangle argument remains in the
separate upstream module.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Wilson
open YangMills.Gluelump.Propagation

noncomputable section

variable {d n nYM : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The free-boundary-box crossing construction supplies exactly the odd-cut
callback required by neutral rectangle reflection. -/
theorem IsTranslationInvariantFreeBoundaryLimit.canonicalRectangleLinkReflectionData
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) :
    CanonicalRectangleLinkReflectionData mu rho hab where
  positive := by
    intro r T
    let w := axisPoint b T
    let p := linkCoordinateCap a b r T
    let O := linkClosedCapsObservable rho a 0 0 w rfl
      (axisPoint_apply_ne hab T) p p rfl rfl
    have hpair : EventuallyLinkCrossingFamilyNormSquare
        (ι := Fin (n * n)) a O := by
      have hcs := eventuallyLinkCrossingFamilyCauchySchwarz_linkClosedCaps
        rho a 0 w rfl (axisPoint_apply_ne hab T) p p
        (linkCoordinateCap_linkPositive hab r T)
        (linkCoordinateCap_linkPositive hab r T)
      filter_upwards [hcs] with N hN
      obtain ⟨F, H, hFH, hFF, hHH⟩ := hN
      exact ⟨F, hFF⟩
    have hpos := hmu.linkCrossingFamilyPositive
      rhoYM hbeta a O hpair
    dsimp [O, linkClosedCapsObservable] at hpos
    simp only [localExpectation, LocalObservable.smul_apply,
      integral_const_mul] at hpos
    have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
    simp only [Complex.mul_im, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero, sub_zero] at hpos
    constructor
    · have him : (∫ A,
          rho.wilsonLoop (linkClosedCoordinateCaps hab r r T) A
            ∂(mu : Measure (Configuration d G))).im = 0 := by
        change (∫ A, rho.wilsonLoop
          (linkClosedCapsPath a 0 0 w rfl (axisPoint_apply_ne hab T)
            p p rfl rfl) A ∂(mu : Measure (Configuration d G))).im = 0
        exact (mul_eq_zero.mp hpos.1).resolve_left (ne_of_gt hn)
      exact him
    · change 0 ≤ (∫ A,
        rho.wilsonLoop (linkClosedCapsPath a 0 0 w rfl
          (axisPoint_apply_ne hab T) p p rfl rfl) A
            ∂(mu : Measure (Configuration d G))).re
      exact (mul_nonneg_iff_of_pos_left hn).mp hpos.2
  cauchySchwarz := by
    intro r s T
    let w := axisPoint b T
    let p := linkCoordinateCap a b r T
    let q := linkCoordinateCap a b s T
    let OFH := linkClosedCapsObservable rho a 0 0 w rfl
      (axisPoint_apply_ne hab T) p q rfl rfl
    let OFF := linkClosedCapsObservable rho a 0 0 w rfl
      (axisPoint_apply_ne hab T) p p rfl rfl
    let OHH := linkClosedCapsObservable rho a 0 0 w rfl
      (axisPoint_apply_ne hab T) q q rfl rfl
    have hcs := hmu.linkCrossingFamilyCauchySchwarz
      (ι := Fin (n * n)) rhoYM hbeta a OFH OFF OHH
      (eventuallyLinkCrossingFamilyCauchySchwarz_linkClosedCaps
        rho a 0 w rfl (axisPoint_apply_ne hab T) p q
        (linkCoordinateCap_linkPositive hab r T)
        (linkCoordinateCap_linkPositive hab s T))
    dsimp [OFH, OFF, OHH, linkClosedCapsObservable] at hcs
    simp only [localExpectation, LocalObservable.smul_apply,
      integral_const_mul] at hcs
    have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
    simp only [Complex.normSq_mul, Complex.normSq_natCast,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] at hcs
    change Complex.normSq (∫ A,
        rho.wilsonLoop (linkClosedCapsPath a 0 0 w rfl
          (axisPoint_apply_ne hab T) p q rfl rfl) A
          ∂(mu : Measure (Configuration d G))) ≤
      (∫ A, rho.wilsonLoop (linkClosedCapsPath a 0 0 w rfl
        (axisPoint_apply_ne hab T) p p rfl rfl) A
        ∂(mu : Measure (Configuration d G))).re *
      (∫ A, rho.wilsonLoop (linkClosedCapsPath a 0 0 w rfl
        (axisPoint_apply_ne hab T) q q rfl rfl) A
        ∂(mu : Measure (Configuration d G))).re
    nlinarith [sq_pos_of_pos hn]

/-- Coordinate-swap invariance of the free-boundary-box limit supplies the
neutral rectangle axis-swap callback. -/
theorem IsTranslationInvariantFreeBoundaryLimit.rectangleAxisSwapInvariant
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n) :
    RectangleAxisSwapInvariant mu rho := by
  intro tau sigma hts a b R T
  unfold rectangleBoundaryIntegral
  have hinvariant := hmu.localExpectation_coordinateSwap
    rhoYM hd hts (rho.wilsonLoop (Path.rectangleBoundary 0 a b R T))
  calc
    (∫ A, rho.wilsonLoop
        (Path.rectangleBoundary 0 (Equiv.swap tau sigma a)
          (Equiv.swap tau sigma b) R T) A
        ∂(mu : Measure (Configuration d G))) =
        ∫ A, rho.wilsonLoop (Path.rectangleBoundary 0 a b R T)
          (diagonalReflectConfiguration tau sigma 0 A)
          ∂(mu : Measure (Configuration d G)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        wilsonLoop_rectangleBoundary_diagonalReflectConfiguration_swap
          rho hts a b R T A
    _ = _ := by
      simpa only [localExpectation,
        LocalObservable.diagonalReflectionPullback_apply] using hinvariant

/-- The full neutral rectangle certificate for the ordinary free-boundary
limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.canonicalRectangleExpectationCertificate
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) :
    CanonicalRectangleExpectationCertificate mu rho hab := by
  let hstate := hmu.reflectionPositiveState rhoYM hbeta hd
  let hlink := hmu.canonicalRectangleLinkReflectionData
    rhoYM hbeta rho hab
  let hswap : RectangleAxisSwapInvariant mu rho :=
    @IsTranslationInvariantFreeBoundaryLimit.rectangleAxisSwapInvariant
      d n nYM G _ _ _ _ _ _ _ _ _ rhoYM beta mu hmu hd rho
  exact YangMills.Gluelump.Propagation.canonicalRectangleExpectationCertificate
    (mu := mu) (rho := rho) (hab := hab) hstate hlink hswap

/-- Translation invariance makes the standard rectangle expectation
independent of its lattice basepoint. -/
theorem IsTranslationInvariantFreeBoundaryLimit.rectangleBoundaryExpectation_basepoint_eq_origin
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (x : Site d) (a b : Fin d) (R T : ℕ) :
    (∫ A, rho.wilsonLoop (Path.rectangleBoundary x a b R T) A
        ∂(mu : Measure (Configuration d G))) =
      rectangleBoundaryIntegral mu rho a b R T := by
  let hstate := hmu.reflectionPositiveState rhoYM hbeta hd
  have htranslate := hstate.localExpectation_translatePullback x
    (rho.wilsonLoop (Path.rectangleBoundary 0 a b R T))
  simpa only [LocalObservable.translatePullback_apply,
    wilsonLoop_rectangleBoundary_translate, rectangleBoundaryIntegral]
      using htranslate

/-- The Wilson rectangle expectation is literally real at every basepoint. -/
theorem IsTranslationInvariantFreeBoundaryLimit.rectangleBoundaryExpectation_im_eq_zero
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b)
    (x : Site d) (R T : ℕ) :
    (∫ A, rho.wilsonLoop (Path.rectangleBoundary x a b R T) A
      ∂(mu : Measure (Configuration d G))).im = 0 := by
  rw [hmu.rectangleBoundaryExpectation_basepoint_eq_origin
    rhoYM hbeta hd rho x a b R T]
  let hstate := hmu.reflectionPositiveState rhoYM hbeta hd
  let hlink := hmu.canonicalRectangleLinkReflectionData
    rhoYM hbeta rho hab
  exact rectangleBoundaryIntegral_im_eq_zero
    (mu := mu) (rho := rho) (hab := hab) hstate hlink R T

/-- Coordinate-label swaps transport rectangle expectations between arbitrary
basepoints.  Translation invariance removes the two basepoints, and the
free-boundary-box swap identity handles the direction labels. -/
theorem IsTranslationInvariantFreeBoundaryLimit.rectangleBoundaryExpectation_axisSwap
    (rhoYM : ContinuousUnitaryRepData G nYM)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      rhoYM.wilsonPotential beta mu)
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    {tau sigma : Fin d} (hts : tau ≠ sigma)
    (x y : Site d) (a b : Fin d) (R T : ℕ) :
    (∫ A, rho.wilsonLoop
        (Path.rectangleBoundary x (Equiv.swap tau sigma a)
          (Equiv.swap tau sigma b) R T) A
        ∂(mu : Measure (Configuration d G))) =
      ∫ A, rho.wilsonLoop (Path.rectangleBoundary y a b R T) A
        ∂(mu : Measure (Configuration d G)) := by
  rw [hmu.rectangleBoundaryExpectation_basepoint_eq_origin
      rhoYM hbeta hd rho x _ _ R T,
    hmu.rectangleBoundaryExpectation_basepoint_eq_origin
      rhoYM hbeta hd rho y a b R T]
  exact hmu.rectangleAxisSwapInvariant rhoYM hd rho hts a b R T

end

end YangMills.StrongCoupling
