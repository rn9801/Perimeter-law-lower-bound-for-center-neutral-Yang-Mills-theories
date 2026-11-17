/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflectionPositivity
import YangMills.Gauge.DiagonalReflectionBridge

/-! Additive Gibbs-law invariance and Hermitian symmetry for the diagonal bridge. -/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- A diagonally symmetric finite Wilson Gibbs law is invariant under the
geometric coordinate-swap reflection.  This is the full-measure symmetry
behind transpose invariance of rectangular Wilson expectations. -/
theorem integral_gibbsMeasure_diagonalReflectConfiguration
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (rho : Wilson.ContinuousUnitaryRepData G n) (beta : ℝ)
    (F : LocalObservable d G) :
    (∫ V, F (diagonalReflectConfiguration τ σ k (Λ.evaluate V))
        ∂FiniteVolume.gibbsMeasure Λ rho.wilsonPotential beta) =
      ∫ V, F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ rho.wilsonPotential beta := by
  let D := Λ.diagonalWilsonDecomposition τ σ k hΛ rho
  let K : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k) → ℂ :=
    fun U =>
      (Real.exp (beta * FiniteVolume.action Λ rho.wilsonPotential
        (Λ.diagonalAssemble τ σ k hΛ U)) /
          FiniteVolume.partitionFunction Λ rho.wilsonPotential beta : ℝ) •
        F (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U))
  have hK : Continuous K := by
    unfold K
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul
          ((FiniteVolume.continuous_action Λ rho.wilsonPotential).comp
            (Λ.diagonalAssemble τ σ k hΛ).continuous))).div_const _)).mul
      (F.toContinuousMap.continuous.comp
        (Λ.continuous_evaluate.comp
          (Λ.diagonalAssemble τ σ k hΛ).continuous))
  have hchange (H : DynamicConfiguration Λ → ℂ) (hH : Continuous H) :
      (∫ U, H (Λ.diagonalAssemble τ σ k hΛ U)
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ V, H V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_diagonalAssemble τ σ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.diagonalAssemble τ σ k hΛ).continuous.measurable.aemeasurable
      hH.aestronglyMeasurable).symm
  rw [FiniteVolume.gibbsMeasure, integral_tilted, integral_tilted]
  let Hleft : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (beta * FiniteVolume.action Λ rho.wilsonPotential V) /
        FiniteVolume.partitionFunction Λ rho.wilsonPotential beta : ℝ) •
      F (diagonalReflectConfiguration τ σ k (Λ.evaluate V))
  let Hright : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (beta * FiniteVolume.action Λ rho.wilsonPotential V) /
        FiniteVolume.partitionFunction Λ rho.wilsonPotential beta : ℝ) •
      F (Λ.evaluate V)
  have hHleft : Continuous Hleft := by
    unfold Hleft
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul
          (FiniteVolume.continuous_action Λ rho.wilsonPotential))).div_const _)).mul
      (F.toContinuousMap.continuous.comp
        ((continuous_diagonalReflectConfiguration τ σ k).comp
          Λ.continuous_evaluate))
  have hHright : Continuous Hright := by
    unfold Hright
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul
          (FiniteVolume.continuous_action Λ rho.wilsonPotential))).div_const _)).mul
      (F.toContinuousMap.continuous.comp Λ.continuous_evaluate)
  change (∫ V, Hleft V ∂Λ.haarMeasure) =
    ∫ V, Hright V ∂Λ.haarMeasure
  rw [← hchange Hleft hHleft, ← hchange Hright hHright]
  have hreflect :
      (∫ U, K (DiagonalReflection.reflect U)
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ U, K U
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar := by
    calc
      (∫ U, K (DiagonalReflection.reflect U)
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) =
          ∫ U, K U ∂Measure.map DiagonalReflection.reflect
            DiagonalReflection.WilsonActionDecomposition.reflectedHaar :=
        (MeasureTheory.integral_map
          DiagonalReflection.continuous_reflect.measurable.aemeasurable
          hK.aestronglyMeasurable).symm
      _ = ∫ U, K U
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar := by
        have hmap : Measure.map
            (DiagonalReflection.reflect :
              DiagonalReflection.ReflectedConfiguration G
                (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k) →
              DiagonalReflection.ReflectedConfiguration G
                (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
            DiagonalReflection.WilsonActionDecomposition.reflectedHaar =
          DiagonalReflection.WilsonActionDecomposition.reflectedHaar :=
          (DiagonalReflection.WilsonActionDecomposition.measurePreserving_reflect
            (G := G) (O := Λ.diagonalPlaneEdges τ σ k)
            (P := Λ.diagonalPositiveEdges τ σ k)).map_eq
        rw [hmap]
  rw [show (fun U => Hright (Λ.diagonalAssemble τ σ k hΛ U)) = K by rfl]
  rw [← hreflect]
  apply integral_congr_ae
  filter_upwards with U
  unfold Hleft K
  rw [Λ.diagonalAssemble_reflect τ σ k hΛ]
  rw [Λ.action_diagonalAssemble τ σ k hΛ rho,
    Λ.action_diagonalAssemble τ σ k hΛ rho, D.action_reflect]

/-- Hermitian symmetry of the concrete normalized finite-volume diagonal
pairing. -/
theorem integral_gibbsMeasure_diagonalReflectionProduct_conj_symm
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (F H : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (hH : H.SupportedInDiagonalPositiveHalf τ σ k) :
    star (∫ V, H.diagonalReflectionProduct τ σ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
      ∫ V, F.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β := by
  rw [Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
      τ σ k hΛ ρ β H F hH hF,
    Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
      τ σ k hΛ ρ β F H hF hH]
  exact (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ)
    |>.reflectionInnerProduct_conj_symm β
      (Λ.diagonalRestrictObservable τ σ k hΛ F)
      (Λ.diagonalRestrictObservable τ σ k hΛ H)

end FiniteSpecification

end


end YangMills.Gauge
