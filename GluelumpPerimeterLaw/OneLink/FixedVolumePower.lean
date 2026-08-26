/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.PowerLowerBound
import GluelumpPerimeterLaw.OneLink.StrictPositivity

/-!
# A power lower bound from one selected finite-volume word

For one fixed specification, continuity of the partition function and of the
selected Taylor amplitude turns its nonzero value at `beta = 0` into a
quantitative `c * beta ^ r` lower bound.  The endpoint factor remains inside
the amplitude norm.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint Propagation
open Filter Set
open scoped Matrix Topology

noncomputable section

variable {d m n N nsigma : ℕ} {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- One word detected at independent Haar gives a fixed-volume power lower
bound with a strictly positive coefficient. -/
theorem transverseOneLink_finite_selectedWord_power_lowerBound
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    (i : Fin n) {r : ℕ}
    (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
      (Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0) nsigma r)
    (hw : (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma).taylorAmplitude
      0 (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i) w ≠ 0) :
    ∃ c > 0, ∃ beta0 > 0, ∀ beta, 0 < beta → beta ≤ beta0 →
      c * beta ^ r ≤ Complex.re
        (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
            (Λ.evaluate A)
          ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  let D := Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma
  let F := transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i
  let Z : ℝ → ℝ := fun beta =>
    FiniteVolume.partitionFunction Λ sigma.wilsonPotential beta
  let K : ℝ := ((2 * nsigma : ℝ)⁻¹) ^ r / r.factorial
  let h : ℝ → ℝ := fun beta =>
    (Z beta)⁻¹ * K * ‖D.taylorAmplitude beta F w‖ ^ 2
  have hZcont : Continuous Z := by
    simpa [Z] using FiniteVolume.continuous_partitionFunction
      Λ sigma.wilsonPotential
  have hZzero : Z 0 = 1 := by simp [Z]
  have hh : ContinuousAt h 0 := by
    have hinv : ContinuousAt (fun beta => (Z beta)⁻¹) 0 :=
      hZcont.continuousAt.inv₀ (by simp [hZzero])
    have hamp : Continuous fun beta => ‖D.taylorAmplitude beta F w‖ ^ 2 :=
      (D.continuous_taylorAmplitude F w).norm.pow 2
    exact (hinv.mul continuousAt_const).mul hamp.continuousAt
  have hK : 0 < K := by
    dsimp [K]
    positivity [sigma.dimension_pos]
  have hh0 : 0 < h 0 := by
    dsimp [h]
    rw [hZzero]
    simp only [inv_one, one_mul]
    exact mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr hw))
  obtain ⟨c, hc, beta0, hbeta0, hlower⟩ :=
    power_lower_bound_of_continuous_factor r hh hh0
  refine ⟨c, hc, beta0, hbeta0, fun beta hbeta hbetaLe => ?_⟩
  have hselected := transverseOneLink_finite_selectedWord_lowerBound
    Λ hd hΛ hclosed sigma rho eta T hT z hz hdyn hbeta.le i w
  apply (hlower beta hbeta hbetaLe).trans
  calc
    beta ^ r * h beta =
        (FiniteVolume.partitionFunction Λ sigma.wilsonPotential beta)⁻¹ *
          (Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient
              D beta r * ‖D.taylorAmplitude beta F w‖ ^ 2) := by
      simp only [h, Z, K,
        Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient]
      rw [div_pow]
      rw [inv_pow]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by simpa [D, F] using hselected

end

end YangMills.Gluelump.OneLink
