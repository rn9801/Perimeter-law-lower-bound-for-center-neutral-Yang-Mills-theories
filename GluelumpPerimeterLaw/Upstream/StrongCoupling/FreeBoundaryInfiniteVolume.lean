/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteLinkReflectionPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryBoxes

/-!
# Translation-invariant free-boundary thermodynamic limits

This module isolates the thermodynamic-limit hypothesis used by the
infinite-volume gluelump perimeter-law statement.  The convergence is tested
against every local continuous observable, which is the exact notion needed
for Wilson loops and screened Wilson lines.

The finite laws are the ordinary free-boundary boxes.  We
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
the ordinary free-boundary reflection boxes when every local observable
converges to its expectation in that measure, independently of the coordinate
direction used to elongate the boxes, and the measure is invariant under
pushforward by every lattice translation. -/
structure IsTranslationInvariantFreeBoundaryLimit
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (μ : ProbabilityMeasure (Configuration d G)) : Prop where
  localLimit : ∀ (τ : Fin d) (F : LocalObservable d G),
    Tendsto (fun n => localExpectation
      (freeBoundaryGibbsSequence Φ β τ n) F) atTop
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

/-- A common local limit is unique, because continuous local observables
determine the probability measure. Thus the paper's uniqueness clause adds
no assumption once the displayed local limits are supplied. -/
theorem IsTranslationInvariantFreeBoundaryLimit.unique
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu nu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    (hnu : IsTranslationInvariantFreeBoundaryLimit Phi beta nu)
    (hd : 0 < d) : mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_integral_localObservable_eq
  intro F
  exact tendsto_nhds_unique
    (hmu.localLimit ⟨0, hd⟩ F) (hnu.localLimit ⟨0, hd⟩ F)

/-- Every fixed centered conditional subsystem is eventually contained
in the paper's free-boundary boxes. Finiteness suffices; no comparison of
boundary conditions at arbitrary coupling is asserted. -/
theorem eventually_centeredToFreeBoundarySubspecification
    (tau : Fin d) (k : ℕ) (eta : Configuration d G) :
    ∀ᶠ radius in atTop,
      Nonempty (FiniteSubspecification (centeredSpecification k eta)
        (freeBoundarySpecification G d radius tau)) := by
  classical
  let E := (centeredSpecification k eta).dynamicEdges ∪
    ((centeredSpecification k eta).activePlaquettes.biUnion fun p =>
      p.boundary.edgeSupport)
  obtain ⟨N, hN⟩ := finiteSupport_subset_linkSymmetricBox tau E
  refine Filter.eventually_atTop.2 ⟨N, fun radius hRadius => ?_⟩
  have hE := hN.trans (linkSymmetricBox_positiveEdges_mono hRadius tau)
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro e he
    exact hE (Finset.mem_union_left _ he)
  · intro p hp
    apply (mem_freeBoundaryActivePlaquettes_iff radius tau p).mpr
    intro e he
    exact hE (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, he⟩))
  · intro p hp
    exact boundary_disjoint_centeredBox_of_not_active hp

/-- At strong coupling the ordinary free-boundary exhaustion has the same
local limit as the centered construction. This uses the existing uniform
boundary estimate only inside its strong-coupling radius. -/
theorem tendsto_freeBoundary_localExpectation_infiniteVolume
    (eta : ℕ → Configuration d G) (Phi : RealPlaquettePotential G) (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound)
    (tau : Fin d) (F : LocalObservable d G) :
    Tendsto (fun radius => localExpectation
      (freeBoundaryGibbsSequence Phi beta tau radius) F) atTop
      (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d)
    F Phi (beta : ℂ)
  let q := plaquetteClusterDecayRate (d := d) Phi (beta : ℂ)
  have hmajorant : Tendsto (fun r : ℕ => B * q ^ r) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (plaquetteClusterDecayRate_pos Phi hbeta).le
      (plaquetteClusterDecayRate_lt_one Phi hbeta)).const_mul B
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.1
    (hmajorant (gt_mem_nhds (half_pos hepsilon)))
  obtain ⟨K, hK⟩ := norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
    F Phi hbeta r
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1
    (tendsto_centered_localExpectation_infiniteVolume eta Phi beta hbeta F)
    (epsilon / 2) (half_pos hepsilon)
  let k := max K J
  have hcenter := hJ k (Nat.le_max_right K J)
  have hsub := eventually_centeredToFreeBoundarySubspecification tau k (eta k)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsub
  refine ⟨N, fun radius hRadius => ?_⟩
  obtain ⟨h⟩ := hN radius hRadius
  have hbound := h.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    (eta k) F Phi beta (B * q ^ r) (fun xi => by
      simpa only [centeredSpecification, B, q] using
        hK k (Nat.le_max_left K J) xi (eta k))
  have hbound' : ‖complexGibbsExpectation F
      (freeBoundarySpecification G d radius tau) Phi (beta : ℂ) -
      complexGibbsExpectation F (centeredSpecification k (eta k)) Phi (beta : ℂ)‖ ≤
      B * q ^ r := by
    simpa only [centeredSpecification] using hbound
  have hcenter' : ‖complexGibbsExpectation F
      (centeredSpecification k (eta k)) Phi (beta : ℂ) -
      ∫ A, F A ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta‖ < epsilon / 2 := by
    simpa only [centeredGibbsSequence, localExpectation_fullGibbsProbability,
      dist_eq_norm] using hcenter
  change dist (localExpectation
    (fullGibbsProbability (freeBoundarySpecification G d radius tau) Phi beta) F) _ < _
  rw [localExpectation_fullGibbsProbability, dist_eq_norm]
  calc
    _ ≤ ‖complexGibbsExpectation F
          (freeBoundarySpecification G d radius tau) Phi (beta : ℂ) -
          complexGibbsExpectation F (centeredSpecification k (eta k)) Phi (beta : ℂ)‖ +
        ‖complexGibbsExpectation F (centeredSpecification k (eta k)) Phi (beta : ℂ) -
          ∫ A, F A ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < epsilon := by
      have htail : B * q ^ r < epsilon / 2 := hr r le_rfl
      linarith

/-- The cluster-constructed strong-coupling probability satisfies the
translation-invariant ordinary free-boundary limit hypothesis. -/
theorem centeredInfiniteVolumeProbability_isTranslationInvariantFreeBoundaryLimit
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    IsTranslationInvariantFreeBoundaryLimit Φ β
      (centeredInfiniteVolumeProbability η Φ β hβ) := by
  constructor
  · intro τ F
    exact tendsto_freeBoundary_localExpectation_infiniteVolume
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
