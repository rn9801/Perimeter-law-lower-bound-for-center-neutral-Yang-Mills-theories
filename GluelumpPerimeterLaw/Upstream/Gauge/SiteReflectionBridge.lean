/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.InfiniteReflection
import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflectionPositivity
import YangMills.Gauge.SiteReflectionBridge

/-! Additive Gibbs-law invariance for the concrete site-reflection bridge. -/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- A site-symmetric finite Wilson Gibbs law is invariant under the geometric
site reflection.  Unlike reflection positivity, this change-of-variables
identity applies to every local observable, with no half-space support
hypothesis. -/
theorem integral_gibbsMeasure_siteReflectConfiguration_eq
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : LocalObservable d G) :
    (∫ V, F (siteReflectConfiguration τ k (Λ.evaluate V))
        ∂FiniteVolume.gibbsMeasure Λ Φ β) =
      ∫ V, F (Λ.evaluate V) ∂FiniteVolume.gibbsMeasure Λ Φ β := by
  let D := SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
    (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
    (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)
  let K : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) → ℂ := fun U =>
    (Real.exp (β * FiniteVolume.action Λ Φ
      (Λ.siteAssemble τ k hΛ U)) /
        FiniteVolume.partitionFunction Λ Φ β : ℝ) •
      F (Λ.evaluate (Λ.siteAssemble τ k hΛ U))
  have hK : Continuous K := by
    unfold K
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul ((FiniteVolume.continuous_action Λ Φ).comp
          (Λ.siteAssemble τ k hΛ).continuous))).div_const _)).mul
      (F.toContinuousMap.continuous.comp
        (Λ.continuous_evaluate.comp (Λ.siteAssemble τ k hΛ).continuous))
  have hchange (H : DynamicConfiguration Λ → ℂ) (hH : Continuous H) :
      (∫ U, H (Λ.siteAssemble τ k hΛ U)
          ∂SiteReflection.reflectedHaar) = ∫ V, H V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_siteAssemble τ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.siteAssemble τ k hΛ).continuous.measurable.aemeasurable
      hH.aestronglyMeasurable).symm
  rw [FiniteVolume.gibbsMeasure, integral_tilted, integral_tilted]
  let Hleft : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ Φ V) /
        FiniteVolume.partitionFunction Λ Φ β : ℝ) •
      F (siteReflectConfiguration τ k (Λ.evaluate V))
  let Hright : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ Φ V) /
        FiniteVolume.partitionFunction Λ Φ β : ℝ) • F (Λ.evaluate V)
  have hHleft : Continuous Hleft := by
    unfold Hleft
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul (FiniteVolume.continuous_action Λ Φ))).div_const _)).mul
      (F.toContinuousMap.continuous.comp
        ((continuous_siteReflectConfiguration τ k).comp Λ.continuous_evaluate))
  have hHright : Continuous Hright := by
    unfold Hright
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul (FiniteVolume.continuous_action Λ Φ))).div_const _)).mul
      (F.toContinuousMap.continuous.comp Λ.continuous_evaluate)
  change (∫ V, Hleft V ∂Λ.haarMeasure) = ∫ V, Hright V ∂Λ.haarMeasure
  rw [← hchange Hleft hHleft, ← hchange Hright hHright]
  have hreflect :
      (∫ U, K (SiteReflection.WilsonActionDecomposition.reflect U)
          ∂SiteReflection.reflectedHaar) =
        ∫ U, K U ∂SiteReflection.reflectedHaar := by
    calc
      (∫ U, K (SiteReflection.WilsonActionDecomposition.reflect U)
          ∂SiteReflection.reflectedHaar) =
          ∫ U, K U ∂Measure.map
            SiteReflection.WilsonActionDecomposition.reflect
              SiteReflection.reflectedHaar :=
        (MeasureTheory.integral_map
          SiteReflection.WilsonActionDecomposition.continuous_reflect.measurable.aemeasurable
          hK.aestronglyMeasurable).symm
      _ = ∫ U, K U ∂SiteReflection.reflectedHaar := by
        rw [(SiteReflection.measurePreserving_reflect
          (G := G) (P := Λ.sitePositiveEdges τ k)
          (O := Λ.sitePlaneEdges τ k)).map_eq]
  rw [show (fun U => Hright (Λ.siteAssemble τ k hΛ U)) = K by rfl]
  rw [← hreflect]
  apply integral_congr_ae
  filter_upwards with U
  unfold Hleft K
  rw [Λ.siteAssemble_reflect τ k hΛ]
  rw [Λ.action_siteAssemble τ k hΛ Φ,
    Λ.action_siteAssemble τ k hΛ Φ,
    SiteReflection.WilsonActionDecomposition.action_reflect]

end FiniteSpecification

end


end YangMills.Gauge
