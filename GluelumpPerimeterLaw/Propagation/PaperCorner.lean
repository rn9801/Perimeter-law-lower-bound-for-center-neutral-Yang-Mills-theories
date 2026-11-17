/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.PaperCornerEndpoints
import GluelumpPerimeterLaw.Propagation.ConjSpanCornerExpectation
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightExpectation
import GluelumpPerimeterLaw.Propagation.CornerReflectionState
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation

/-!
# The paper's bend and close inequalities at every positive length

The long comb direction lies outside the rectangle plane. The short in-plane
support has width one, so the two parity cases give the corner inequalities
for all positive physical lengths, without a screening-degree cutoff.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
  Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [YangMills.Gauge.GaugeHaarProbability G]

/-- The L-shaped observable produced by bending an affine straight arm with
left radius `s` and right radius `t`. -/
def paperCornerBentObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (s t : ℕ) : LocalObservable d G :=
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₂ hd
  let hab := Geometry.armAxis_ne_transverseAxis₂ hd
  let Phi := conjSpanCornerFarEndpoint hd sigma rho T t
  screenedObservable rho (Phi.diagonalPullback a b (-(s : ℤ))) Phi
    (conjSpanCornerLowerLPath hab s t)

/-- The real bent expectation at physical length `length`, split into its
two half-arm lengths. Both even and odd lengths are used below. -/
def paperCornerBentExpectation
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (length : ℕ) : ℝ :=
  let s := length / 2
  let t := length - s
  Complex.re (∫ A, paperCornerBentObservable
    hd sigma rho T s t A ∂(mu : Measure (Configuration d G)))

@[simp]
theorem paperCornerBentExpectation_odd
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) =
      Complex.re (∫ A, paperCornerBentObservable
        hd sigma rho T l (l + 1) A
          ∂(mu : Measure (Configuration d G))) := by
  have hs : (2 * l + 1) / 2 = l := by omega
  have ht : 2 * l + 1 - l = l + 1 := by omega
  simp [paperCornerBentExpectation, hs, ht]

@[simp]
theorem paperCornerBentExpectation_even
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    paperCornerBentExpectation mu hd sigma rho T (2 * l) =
      Complex.re (∫ A, paperCornerBentObservable
        hd sigma rho T l l A
          ∂(mu : Measure (Configuration d G))) := by
  have hs : (2 * l) / 2 = l := by omega
  have ht : 2 * l - l = l := by omega
  simp [paperCornerBentExpectation, hs, ht]

@[simp]
theorem paperCornerSquareExpectation_even
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    {a b : Fin d} (hab : a ≠ b) (l : ℕ) :
    conjSpanCornerSquareExpectation mu rho hab (2 * l) =
      Complex.re (∫ A, rho.wilsonLoop
        (conjSpanCornerSquareLoop hab l l) A
          ∂(mu : Measure (Configuration d G))) := by
  have hs : (2 * l) / 2 = l := by omega
  have ht : 2 * l - l = l := by omega
  dsimp only [conjSpanCornerSquareExpectation]
  rw [hs, ht]

/-- The source cast in the geometric lower L does not alter the screened
observable produced by diagonal row bending. -/
theorem screenedObservable_paperCornerLowerLPath_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (s t : ℕ) (A : Configuration d G) :
    paperCornerBentObservable hd sigma rho T s t A =
      let a := Geometry.armAxis hd
      let b := Geometry.transverseAxis₂ hd
      let hab := Geometry.armAxis_ne_transverseAxis₂ hd
      let Phi := conjSpanCornerFarEndpoint hd sigma rho T t
      let p := conjSpanCornerArmToOrigin a s t
      screenedObservable rho (Phi.diagonalPullback a b (-(s : ℤ))) Phi
        ((diagonalReflectedPathToFixed hab (-(s : ℤ)) p
          (diagonalReflection_conjSpanCornerOriginSite_fixed hab s)).comp
            p.reverse) A := by
  simp [paperCornerBentObservable, conjSpanCornerLowerLPath,
    screenedObservable_apply, screenedValue, holonomy_castSource]

theorem paperPhysicalStraightExpectation_sq_le_cornerBent_odd
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l + 1) ^ 2 ≤
      paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) := by
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₂ hd
  let hab := Geometry.armAxis_ne_transverseAxis₂ hd
  let Phi := conjSpanCornerFarEndpoint hd sigma rho T (l + 1)
  let Xi := paperOddCornerComparisonEndpoint hd sigma rho T l
  let p := conjSpanCornerArmToOrigin a l (l + 1)
  have hPhi : Phi.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) :=
    paperCornerFarEndpoint_supportedInDiagonalPositiveHalf
      hd sigma rho T l (l + 1) (by omega)
  have hp : Endpoint.Path.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) p :=
    conjSpanCornerArmToOrigin_supportedInDiagonalPositiveHalf hab l (l + 1)
  have hXi : Xi.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) :=
    paperOddCornerComparisonEndpoint_supportedInDiagonalPositiveHalf
      hd sigma rho T l
  have hXiNorm : ∀ A, endpointL2Norm (Xi A) ≤ 1 :=
    paperOddCornerComparisonEndpoint_l2Norm_le_one hd sigma rho T l
  have hrow :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.diagonalRowBending
      hstate rho Phi Xi hab (-(l : ℤ)) p
    (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)
    hPhi hp hXi hXiNorm
  have hherm :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.diagonalBentIntegral_eq_star_reverse
      hstate rho Phi Xi hab (-(l : ℤ)) p
    (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)
    hPhi hp hXi
  let I : ℂ := ∫ A, conjSpanPhysicalStraightObservable
    hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd) (2 * l + 1) A
      ∂(mu : Measure (Configuration d G))
  let B : ℂ := ∫ A,
    screenedObservable rho (Phi.diagonalPullback a b (-(l : ℤ))) Xi
      (diagonalReflectedPathToFixed hab (-(l : ℤ)) p
        (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)) A
      ∂(mu : Measure (Configuration d G))
  have hreverse :
      (∫ A, screenedObservable rho
        (Xi.diagonalPullback a b (-(l : ℤ))) Phi p.reverse A
          ∂(mu : Measure (Configuration d G))) = I := by
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      have hXiPull : Xi.diagonalPullback a b (-(l : ℤ)) A =
          conjSpanOddCornerOriginEndpoint hd sigma rho T l A := by
        simp only [Xi, paperOddCornerComparisonEndpoint,
          LocalField.diagonalPullback_apply]
        rw [diagonalReflectConfiguration_diagonalReflectConfiguration hab]
      rw [screenedObservable_apply]
      unfold screenedValue
      rw [hXiPull]
      simpa only [screenedObservable_apply, screenedValue] using
        conjSpanOddCornerStraight_reverse_apply_eq_physical
          hd sigma rho T l A
  have hBI : B = star I := by
    calc
      B = star (∫ A, screenedObservable rho
          (Xi.diagonalPullback a b (-(l : ℤ))) Phi p.reverse A
            ∂(mu : Measure (Configuration d G))) := by
        simpa [B, a, b, hab, Phi, Xi, p] using hherm
      _ = star I := congrArg star hreverse
  have hL :
      Complex.re (∫ A, screenedObservable rho
        (Phi.diagonalPullback a b (-(l : ℤ))) Phi
          ((diagonalReflectedPathToFixed hab (-(l : ℤ)) p
            (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)).comp
              p.reverse) A ∂(mu : Measure (Configuration d G))) =
        paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) := by
    rw [paperCornerBentExpectation_odd]
    apply congrArg Complex.re
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      simpa [a, b, hab, Phi, p] using
        (screenedObservable_paperCornerLowerLPath_apply
          hd sigma rho T l (l + 1) A).symm
  calc
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l + 1) ^ 2 = I.re ^ 2 := rfl
    _ ≤ Complex.normSq I := by
      simpa [pow_two] using Complex.re_sq_le_normSq I
    _ = Complex.normSq B := by rw [hBI]; simp
    _ ≤ Complex.re (∫ A, screenedObservable rho
        (Phi.diagonalPullback a b (-(l : ℤ))) Phi
          ((diagonalReflectedPathToFixed hab (-(l : ℤ)) p
            (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)).comp
              p.reverse) A ∂(mu : Measure (Configuration d G))) := hrow
    _ = _ := hL

theorem paperPhysicalStraightExpectation_sq_le_cornerBent_even
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (hl : 0 < l) :
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l) ^ 2 ≤
      paperCornerBentExpectation mu hd sigma rho T (2 * l) := by
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₂ hd
  let hab := Geometry.armAxis_ne_transverseAxis₂ hd
  let Phi := conjSpanCornerFarEndpoint hd sigma rho T l
  let Xi := paperEvenCornerComparisonEndpoint hd sigma rho T l
  let p := conjSpanCornerArmToOrigin a l l
  have hPhi : Phi.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) :=
    paperCornerFarEndpoint_supportedInDiagonalPositiveHalf
      hd sigma rho T l l (by omega)
  have hp : Endpoint.Path.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) p :=
    conjSpanCornerArmToOrigin_supportedInDiagonalPositiveHalf hab l l
  have hXi : Xi.SupportedInDiagonalPositiveHalf a b (-(l : ℤ)) :=
    paperEvenCornerComparisonEndpoint_supportedInDiagonalPositiveHalf
      hd sigma rho T l
  have hXiNorm : ∀ A, endpointL2Norm (Xi A) ≤ 1 :=
    paperEvenCornerComparisonEndpoint_l2Norm_le_one hd sigma rho T l
  have hrow :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.diagonalRowBending
      hstate rho Phi Xi hab (-(l : ℤ)) p
    (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)
    hPhi hp hXi hXiNorm
  have hherm :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.diagonalBentIntegral_eq_star_reverse
      hstate rho Phi Xi hab (-(l : ℤ)) p
    (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)
    hPhi hp hXi
  let I : ℂ := ∫ A, conjSpanPhysicalStraightObservable
    hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd) (2 * l) A
      ∂(mu : Measure (Configuration d G))
  let B : ℂ := ∫ A,
    screenedObservable rho (Phi.diagonalPullback a b (-(l : ℤ))) Xi
      (diagonalReflectedPathToFixed hab (-(l : ℤ)) p
        (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)) A
      ∂(mu : Measure (Configuration d G))
  have hreverse :
      (∫ A, screenedObservable rho
        (Xi.diagonalPullback a b (-(l : ℤ))) Phi p.reverse A
          ∂(mu : Measure (Configuration d G))) = I := by
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      have hXiPull : Xi.diagonalPullback a b (-(l : ℤ)) A =
          conjSpanEvenCornerOriginEndpoint hd sigma rho T l A := by
        simp only [Xi, paperEvenCornerComparisonEndpoint,
          LocalField.diagonalPullback_apply]
        rw [diagonalReflectConfiguration_diagonalReflectConfiguration hab]
      rw [screenedObservable_apply]
      unfold screenedValue
      rw [hXiPull]
      simpa only [screenedObservable_apply, screenedValue] using
        conjSpanEvenCornerStraight_reverse_apply_eq_physical
          hd sigma rho T l A
  have hBI : B = star I := by
    calc
      B = star (∫ A, screenedObservable rho
          (Xi.diagonalPullback a b (-(l : ℤ))) Phi p.reverse A
            ∂(mu : Measure (Configuration d G))) := by
        simpa [B, a, b, hab, Phi, Xi, p] using hherm
      _ = star I := congrArg star hreverse
  have hL :
      Complex.re (∫ A, screenedObservable rho
        (Phi.diagonalPullback a b (-(l : ℤ))) Phi
          ((diagonalReflectedPathToFixed hab (-(l : ℤ)) p
            (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)).comp
              p.reverse) A ∂(mu : Measure (Configuration d G))) =
        paperCornerBentExpectation mu hd sigma rho T (2 * l) := by
    rw [paperCornerBentExpectation_even]
    apply congrArg Complex.re
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      simpa [a, b, hab, Phi, p] using
        (screenedObservable_paperCornerLowerLPath_apply
          hd sigma rho T l l A).symm
  calc
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l) ^ 2 = I.re ^ 2 := rfl
    _ ≤ Complex.normSq I := by
      simpa [pow_two] using Complex.re_sq_le_normSq I
    _ = Complex.normSq B := by rw [hBI]; simp
    _ ≤ Complex.re (∫ A, screenedObservable rho
        (Phi.diagonalPullback a b (-(l : ℤ))) Phi
          ((diagonalReflectedPathToFixed hab (-(l : ℤ)) p
            (diagonalReflection_conjSpanCornerOriginSite_fixed hab l)).comp
              p.reverse) A ∂(mu : Measure (Configuration d G))) := hrow
    _ = _ := hL

theorem paperCornerBent_sq_div_dimension_le_square_odd
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) ^ 2 /
        (r : ℝ) ≤
      conjSpanCornerSquareExpectation mu rho
        (Geometry.armAxis_ne_transverseAxis₂ hd) (2 * l + 1) := by
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₂ hd
  let hab := Geometry.armAxis_ne_transverseAxis₂ hd
  let Phi := conjSpanCornerFarEndpoint hd sigma rho T (l + 1)
  let Psi := Phi.diagonalPullback a b (-(l : ℤ))
  have hp : Endpoint.Path.SupportedInAntiDiagonalPositiveHalf a b (l + 1)
      (conjSpanCornerUpperLPath hab l (l + 1)) :=
    conjSpanCornerUpperLPath_supportedInAntiDiagonalPositiveHalf
      hab l (l + 1)
  have hPhi : Phi.SupportedInAntiDiagonalPositiveHalf a b (l + 1) :=
    paperCornerFarEndpoint_supportedInAntiDiagonalPositiveHalf
      hd sigma rho T (l + 1)
  have hPsi : Psi.SupportedInAntiDiagonalPositiveHalf a b (l + 1) :=
    paperCornerFarEndpoint_diagonalPullback_supportedInAntiDiagonalPositiveHalf
      hd sigma rho T l (l + 1)
  have hPhiNorm : ∀ A, endpointL2Norm (Phi A) ≤ 1 :=
    conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T (l + 1)
  have hPsiNorm : ∀ A, endpointL2Norm (Psi A) ≤ 1 := by
    intro A
    change endpointL2Norm (Phi (diagonalReflectConfiguration
      a b (-(l : ℤ)) A)) ≤ 1
    exact hPhiNorm _
  have hclose :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.antiDiagonalMatrixClosing
      hstate rho Psi Phi hab (l + 1)
    (conjSpanCornerUpperLPath hab l (l + 1))
    (antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed hab l (l + 1))
    (antiDiagonalReflection_conjSpanCornerFarSite_fixed hab l (l + 1))
    hp hPsi hPhi hPsiNorm hPhiNorm
  have hreflect :
      antiDiagonalReflectedPathFixed hab ((l : ℤ) + 1)
        (conjSpanCornerUpperLPath hab l (l + 1))
        (antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed
          hab l (l + 1))
        (antiDiagonalReflection_conjSpanCornerFarSite_fixed
          hab l (l + 1)) =
      conjSpanCornerLowerLPath hab l (l + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      antiDiagonalReflected_conjSpanCornerUpperLPath_eq_lower
        hab l (l + 1)
  rw [hreflect] at hclose
  have hBent :
      paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) =
        Complex.re (∫ A, screenedObservable rho Psi Phi
          (conjSpanCornerLowerLPath hab l (l + 1)) A
            ∂(mu : Measure (Configuration d G))) := by
    simp [paperCornerBentExpectation_odd,
      paperCornerBentObservable, a, b, hab, Phi, Psi]
  have hSq :
      conjSpanCornerSquareExpectation mu rho hab (2 * l + 1) =
        Complex.re (∫ A, rho.wilsonLoop
          (conjSpanCornerSquareLoop hab l (l + 1)) A
            ∂(mu : Measure (Configuration d G))) :=
    conjSpanCornerSquareExpectation_odd mu rho hab l
  have hrealSq :
      paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) ^ 2 ≤
        (r : ℝ) * conjSpanCornerSquareExpectation mu rho hab (2 * l + 1) := by
    rw [hBent, hSq]
    simpa [pow_two] using (Complex.re_sq_le_normSq _).trans (by
      simpa [conjSpanCornerSquareLoop, a, b, hab, Phi, Psi] using hclose)
  have hr : (0 : ℝ) < r := by exact_mod_cast rho.dimension_pos
  calc
    paperCornerBentExpectation mu hd sigma rho T (2 * l + 1) ^ 2 /
        (r : ℝ) ≤
      ((r : ℝ) * conjSpanCornerSquareExpectation mu rho hab (2 * l + 1)) /
        (r : ℝ) := div_le_div_of_nonneg_right hrealSq hr.le
    _ = conjSpanCornerSquareExpectation mu rho hab (2 * l + 1) := by
      field_simp

theorem paperCornerBent_sq_div_dimension_le_square_even
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    paperCornerBentExpectation mu hd sigma rho T (2 * l) ^ 2 /
        (r : ℝ) ≤
      conjSpanCornerSquareExpectation mu rho
        (Geometry.armAxis_ne_transverseAxis₂ hd) (2 * l) := by
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₂ hd
  let hab := Geometry.armAxis_ne_transverseAxis₂ hd
  let Phi := conjSpanCornerFarEndpoint hd sigma rho T l
  let Psi := Phi.diagonalPullback a b (-(l : ℤ))
  have hp : Endpoint.Path.SupportedInAntiDiagonalPositiveHalf a b l
      (conjSpanCornerUpperLPath hab l l) :=
    conjSpanCornerUpperLPath_supportedInAntiDiagonalPositiveHalf
      hab l l
  have hPhi : Phi.SupportedInAntiDiagonalPositiveHalf a b l :=
    paperCornerFarEndpoint_supportedInAntiDiagonalPositiveHalf
      hd sigma rho T l
  have hPsi : Psi.SupportedInAntiDiagonalPositiveHalf a b l :=
    paperCornerFarEndpoint_diagonalPullback_supportedInAntiDiagonalPositiveHalf
      hd sigma rho T l l
  have hPhiNorm : ∀ A, endpointL2Norm (Phi A) ≤ 1 :=
    conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T l
  have hPsiNorm : ∀ A, endpointL2Norm (Psi A) ≤ 1 := by
    intro A
    change endpointL2Norm (Phi (diagonalReflectConfiguration
      a b (-(l : ℤ)) A)) ≤ 1
    exact hPhiNorm _
  have hclose :=
    YangMills.Gluelump.Propagation.Gauge.ReflectionPositiveState.antiDiagonalMatrixClosing
      hstate rho Psi Phi hab l
    (conjSpanCornerUpperLPath hab l l)
    (antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed hab l l)
    (antiDiagonalReflection_conjSpanCornerFarSite_fixed hab l l)
    hp hPsi hPhi hPsiNorm hPhiNorm
  have hreflect :
      antiDiagonalReflectedPathFixed hab (l : ℤ)
        (conjSpanCornerUpperLPath hab l l)
        (antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed
          hab l l)
        (antiDiagonalReflection_conjSpanCornerFarSite_fixed
          hab l l) =
      conjSpanCornerLowerLPath hab l l := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      antiDiagonalReflected_conjSpanCornerUpperLPath_eq_lower
        hab l l
  rw [hreflect] at hclose
  have hBent :
      paperCornerBentExpectation mu hd sigma rho T (2 * l) =
        Complex.re (∫ A, screenedObservable rho Psi Phi
          (conjSpanCornerLowerLPath hab l l) A
            ∂(mu : Measure (Configuration d G))) := by
    simp [paperCornerBentExpectation_even,
      paperCornerBentObservable, a, b, hab, Phi, Psi]
  have hSq :
      conjSpanCornerSquareExpectation mu rho hab (2 * l) =
        Complex.re (∫ A, rho.wilsonLoop
          (conjSpanCornerSquareLoop hab l l) A
            ∂(mu : Measure (Configuration d G))) :=
    paperCornerSquareExpectation_even mu rho hab l
  have hrealSq :
      paperCornerBentExpectation mu hd sigma rho T (2 * l) ^ 2 ≤
        (r : ℝ) * conjSpanCornerSquareExpectation mu rho hab (2 * l) := by
    rw [hBent, hSq]
    simpa [pow_two] using (Complex.re_sq_le_normSq _).trans (by
      simpa [conjSpanCornerSquareLoop, a, b, hab, Phi, Psi] using hclose)
  have hr : (0 : ℝ) < r := by exact_mod_cast rho.dimension_pos
  calc
    paperCornerBentExpectation mu hd sigma rho T (2 * l) ^ 2 /
        (r : ℝ) ≤
      ((r : ℝ) * conjSpanCornerSquareExpectation mu rho hab (2 * l)) /
        (r : ℝ) := div_le_div_of_nonneg_right hrealSq hr.le
    _ = conjSpanCornerSquareExpectation mu rho hab (2 * l) := by
      field_simp

/-- The paper's first diagonal inequality at every positive length. -/
theorem paperPhysicalStraightExpectation_sq_le_cornerBent
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (length : ℕ) (hlength : 0 < length) :
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) length ^ 2 ≤
      paperCornerBentExpectation mu hd sigma rho T length := by
  by_cases heven : length % 2 = 0
  · have hlengthEq : length = 2 * (length / 2) := by omega
    rw [hlengthEq]
    exact paperPhysicalStraightExpectation_sq_le_cornerBent_even
      mu hstate hd sigma rho T (length / 2) (by omega)
  · have hlengthEq : length = 2 * (length / 2) + 1 := by omega
    rw [hlengthEq]
    exact paperPhysicalStraightExpectation_sq_le_cornerBent_odd
      mu hstate hd sigma rho T (length / 2)

/-- The paper's second diagonal inequality, closing every square size. -/
theorem paperCornerBent_sq_div_dimension_le_square
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (length : ℕ) :
    paperCornerBentExpectation mu hd sigma rho T length ^ 2 / (r : ℝ) ≤
      canonicalRectangleExpectation mu rho
        (Geometry.armAxis_ne_transverseAxis₂ hd) length length := by
  rw [← conjSpanCornerSquareExpectation_eq_canonicalRectangleExpectation
    mu hstate rho (Geometry.armAxis_ne_transverseAxis₂ hd) length]
  by_cases heven : length % 2 = 0
  · have hlengthEq : length = 2 * (length / 2) := by omega
    rw [hlengthEq]
    exact paperCornerBent_sq_div_dimension_le_square_even
      mu hstate hd sigma rho T (length / 2)
  · have hlengthEq : length = 2 * (length / 2) + 1 := by omega
    rw [hlengthEq]
    exact paperCornerBent_sq_div_dimension_le_square_odd
      mu hstate hd sigma rho T (length / 2)

/-- The paper's square estimate, at every positive side length. -/
theorem paperSquare_lower_bound_of_line_rate
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) {q : ℝ} (hq : 0 < q)
    (hline : ∀ length, 0 < length → q ^ length ≤
      conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) length)
    {length : ℕ} (hlength : 0 < length) :
    q ^ (4 * length) / (r : ℝ) ≤ canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) length length := by
  have hbend := paperPhysicalStraightExpectation_sq_le_cornerBent
    mu hstate hd sigma rho T length hlength
  have hseed : (q ^ length) ^ 2 ≤
      paperCornerBentExpectation mu hd sigma rho T length :=
    (pow_le_pow_left₀ (pow_nonneg hq.le _) (hline length hlength) 2).trans hbend
  have hfour : q ^ (4 * length) ≤
      paperCornerBentExpectation mu hd sigma rho T length ^ 2 := by
    calc
      q ^ (4 * length) = ((q ^ length) ^ 2) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hseed 2
  have hr : (0 : ℝ) < r := by exact_mod_cast rho.dimension_pos
  exact (div_le_div_of_nonneg_right hfour hr.le).trans
    (paperCornerBent_sq_div_dimension_le_square mu hstate hd sigma rho T length)

/-- Enlarge to the square of side `max(R,S)`, exactly as in the paper.
No collar enlargement or parity restriction remains. -/
theorem paperRectangle_lower_bound_of_line_rate
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hrect : CanonicalRectangleExpectationCertificate mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd))
    {q : ℝ} (hq : 0 < q)
    (hline : ∀ length, 0 < length → q ^ length ≤
      conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) length)
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) :
    q ^ (4 * max R S) / (r : ℝ) ≤ canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) R S := by
  let N := max R S
  have hN : 0 < N := hR.trans_le (Nat.le_max_left R S)
  have hr : (0 : ℝ) < r := by exact_mod_cast rho.dimension_pos
  have hdiag : 0 < canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) 1 1 :=
    (div_pos (pow_pos hq _) hr).trans_le
      (paperSquare_lower_bound_of_line_rate mu hstate hd sigma rho T hq hline (by omega))
  have hrowOne : ∀ t, 0 < canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) 1 t :=
    positive_of_reflectionLogConvex_of_pos
      (hrect.side_logConvex 1) (hrect.nonnegative 1) (by omega) hdiag
  have hpos (R : ℕ) : ∀ t, 0 < canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) R t := by
    have hRone : 0 < canonicalRectangleExpectation mu rho
        (Geometry.armAxis_ne_transverseAxis₂ hd) R 1 := by
      rw [hrect.transpose R 1]
      exact hrowOne R
    exact positive_of_reflectionLogConvex_of_pos
      (hrect.side_logConvex R) (hrect.nonnegative R) (by omega) hRone
  have hanti (R : ℕ) : Antitone (canonicalRectangleExpectation mu rho
      (Geometry.armAxis_ne_transverseAxis₂ hd) R) :=
    antitone_of_reflectionLogConvex_of_le_one
      (hrect.side_logConvex R) (hpos R) (hrect.le_one R)
  have hfirst := (hanti N (Nat.le_max_left R S)).trans_eq (hrect.transpose N R)
  exact (paperSquare_lower_bound_of_line_rate
    mu hstate hd sigma rho T hq hline hN).trans
      (hfirst.trans (hanti R (Nat.le_max_right R S)))

end

end YangMills.Gluelump.Propagation
