/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteLinkReflectionPositivity

/-!
# Translation-invariant free-boundary thermodynamic limits

This module isolates the thermodynamic-limit hypothesis used by the
infinite-volume gluelump perimeter-law statement.  The convergence is tested
against every local continuous observable, which is the exact notion needed
for Wilson loops and screened Wilson lines.

The finite laws are the completed link-symmetric free-boundary boxes.  We
require the same limit in every distinguished coordinate direction.  This is
the shape-independence needed later to inherit all reflection inequalities in
one common measure: link reflection uses the box elongated in its normal
direction, while in dimension at least three site and diagonal reflections
can use an elongated direction transverse to their cutting coordinates.

At strong coupling this is not an additional assumption.  The cluster
expansion proves convergence of every such exhaustion to the existing
centered infinite-volume probability and proves translation invariance of
that probability.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- A probability measure is a translation-invariant thermodynamic limit of
the completed free-boundary reflection boxes when every local observable
converges to its expectation in that measure, independently of the coordinate
direction used to elongate the boxes, and the measure is invariant under
pushforward by every lattice translation. -/
structure IsTranslationInvariantFreeBoundaryLimit
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (μ : ProbabilityMeasure (Configuration d G)) : Prop where
  localLimit : ∀ (τ : Fin d) (F : LocalObservable d G),
    Tendsto (fun n => localExpectation
      (linkSymmetricGibbsSequence Φ β τ n) F) atTop
      (nhds (localExpectation μ F))
  translationInvariant : ∀ v : Site d,
    Measure.map (LocalObservable.translateConfiguration (G := G) v)
        (μ : Measure (Configuration d G)) =
      (μ : Measure (Configuration d G))

omit [CompactSpace G] [T2Space G] in
/-- Translation invariance of the limiting measure gives the expectation
identity consumed by the reflection-propagation layer. -/
theorem IsTranslationInvariantFreeBoundaryLimit.localExpectation_translatePullback
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    (v : Site d) (F : LocalObservable d G) :
    localExpectation mu (F.translatePullback v) = localExpectation mu F := by
  have hv :=
    (LocalObservable.continuous_translateConfiguration (G := G) v).measurable
  change (∫ A, F (LocalObservable.translateConfiguration v A)
      ∂(mu : Measure (Configuration d G))) =
    ∫ A, F A ∂(mu : Measure (Configuration d G))
  calc
    _ = ∫ A, F A ∂Measure.map
        (LocalObservable.translateConfiguration (G := G) v)
        (mu : Measure (Configuration d G)) := by
      rw [MeasureTheory.integral_map hv.aemeasurable
        F.toContinuousMap.continuous.aestronglyMeasurable]
    _ = _ := by rw [h.translationInvariant v]

/-- The cluster-constructed strong-coupling probability satisfies the
translation-invariant completed-free-boundary limit hypothesis. -/
theorem centeredInfiniteVolumeProbability_isTranslationInvariantFreeBoundaryLimit
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    IsTranslationInvariantFreeBoundaryLimit Φ β
      (centeredInfiniteVolumeProbability η Φ β hβ) := by
  constructor
  · intro τ F
    exact tendsto_linkSymmetric_localExpectation_infiniteVolume
      η Φ β hβ τ F
  · intro v
    change Measure.map
      (LocalObservable.translateConfiguration (G := G) v)
      (centeredInfiniteVolumeMeasure η Φ β hβ) =
        centeredInfiniteVolumeMeasure η Φ β hβ
    have hv :=
      (LocalObservable.continuous_translateConfiguration (G := G) v).measurable
    letI : IsProbabilityMeasure
        (Measure.map
          (LocalObservable.translateConfiguration (G := G) v)
          (centeredInfiniteVolumeMeasure η Φ β hβ)) :=
      Measure.isProbabilityMeasure_map hv.aemeasurable
    apply measure_eq_of_integral_localObservable_eq
    intro F
    rw [MeasureTheory.integral_map hv.aemeasurable
      F.toContinuousMap.continuous.aestronglyMeasurable]
    exact centeredInfiniteVolume_integral_translatePullback
      η Φ β hβ v F

/-- In particular, the strong-coupling Wilson state constructed with constant
identity exterior data satisfies the limit hypothesis used by the gluelump
perimeter-law target. -/
theorem wilsonStrongCoupling_isTranslationInvariantFreeBoundaryLimit
    {n : ℕ} (sigma : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d sigma.wilsonPotential.bound) :
    IsTranslationInvariantFreeBoundaryLimit sigma.wilsonPotential β
      (centeredInfiniteVolumeProbability
        (fun _ ↦ (1 : Configuration d G)) sigma.wilsonPotential β hβ) :=
  centeredInfiniteVolumeProbability_isTranslationInvariantFreeBoundaryLimit
    (fun _ ↦ (1 : Configuration d G)) sigma.wilsonPotential β hβ

end

end YangMills.StrongCoupling
