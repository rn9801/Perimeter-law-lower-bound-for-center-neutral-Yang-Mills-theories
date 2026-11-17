/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflectionBridge
import YangMills.StrongCoupling.ConcreteSiteReflectionPositivity

/-! Additive site-reflection invariance results used by this package. -/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The centered identity-exterior finite Gibbs law is invariant under a
coordinate flip through the origin, tested against every local observable. -/
theorem centeredGibbsSequence_one_integral_siteReflectionPullback
    (Φ : RealPlaquettePotential G) (β : ℝ) (n : ℕ) (τ : Fin d)
    (F : LocalObservable d G) :
    localExpectation
        (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n)
        (F.siteReflectionPullback τ 0) =
      localExpectation
        (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n) F := by
  let Λ := centeredSpecification n (1 : Configuration d G)
  simp only [centeredGibbsSequence, localExpectation_fullGibbsProbability]
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  simp only [LocalObservable.siteReflectionPullback_apply]
  change (∫ V, F (siteReflectConfiguration τ 0 (Λ.evaluate V))
      ∂Gauge.FiniteVolume.gibbsMeasure Λ Φ β) =
    ∫ V, F (Λ.evaluate V) ∂Gauge.FiniteVolume.gibbsMeasure Λ Φ β
  exact Λ.integral_gibbsMeasure_siteReflectConfiguration_eq τ 0
    (centeredSpecification_one_siteSymmetric n τ) Φ β F

/-- The strong-coupling infinite-volume Yang--Mills state is invariant under
reflection of any coordinate through the origin. -/
theorem centeredInfiniteVolume_integral_siteReflectionPullback
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (F : LocalObservable d G) :
    ∫ A, F (siteReflectConfiguration τ 0 A)
        ∂centeredInfiniteVolumeMeasure η Φ β hβ =
      ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
  let oneExterior : ℕ → Configuration d G := fun _ => 1
  have hleft := tendsto_centered_localExpectation_infiniteVolume
    oneExterior Φ β hβ (F.siteReflectionPullback τ 0)
  have hright := tendsto_centered_localExpectation_infiniteVolume
    oneExterior Φ β hβ F
  have heq : (fun n => localExpectation
      (centeredGibbsSequence oneExterior Φ β n)
        (F.siteReflectionPullback τ 0)) =
      fun n => localExpectation (centeredGibbsSequence oneExterior Φ β n) F := by
    funext n
    exact centeredGibbsSequence_one_integral_siteReflectionPullback Φ β n τ F
  rw [heq] at hleft
  have hlimits := tendsto_nhds_unique hleft hright
  have hlimits' :
      (∫ A, F (siteReflectConfiguration τ 0 A)
          ∂centeredInfiniteVolumeMeasure oneExterior Φ β hβ) =
        ∫ A, F A ∂centeredInfiniteVolumeMeasure oneExterior Φ β hβ := by
    simpa only [LocalObservable.siteReflectionPullback_apply] using hlimits
  have hboundary := centeredInfiniteVolumeMeasure_boundary_independent
    oneExterior η Φ β hβ
  calc
    (∫ A, F (siteReflectConfiguration τ 0 A)
        ∂centeredInfiniteVolumeMeasure η Φ β hβ) =
        ∫ A, F A
          ∂centeredInfiniteVolumeMeasure oneExterior Φ β hβ := by
      rw [← hboundary]
      exact hlimits'
    _ = ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
      rw [hboundary]

/-- Pushforward form of coordinate-reflection invariance of the
strong-coupling infinite-volume Yang--Mills probability. -/
theorem centeredInfiniteVolumeMeasure_map_siteReflectConfiguration
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) :
    Measure.map (siteReflectConfiguration τ 0)
        (centeredInfiniteVolumeMeasure η Φ β hβ) =
      centeredInfiniteVolumeMeasure η Φ β hβ := by
  have hreflect : Measurable (siteReflectConfiguration (G := G) τ 0) :=
    (continuous_siteReflectConfiguration τ 0).measurable
  letI : IsProbabilityMeasure
      (Measure.map (siteReflectConfiguration τ 0)
        (centeredInfiniteVolumeMeasure η Φ β hβ)) :=
    Measure.isProbabilityMeasure_map hreflect.aemeasurable
  apply measure_eq_of_integral_localObservable_eq
  intro F
  rw [MeasureTheory.integral_map hreflect.aemeasurable
    F.toContinuousMap.continuous.aestronglyMeasurable]
  exact centeredInfiniteVolume_integral_siteReflectionPullback
    η Φ β hβ τ F

end

end YangMills.StrongCoupling
