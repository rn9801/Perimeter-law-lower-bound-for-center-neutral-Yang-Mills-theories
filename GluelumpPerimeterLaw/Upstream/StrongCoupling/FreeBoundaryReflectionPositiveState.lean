/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryInfiniteVolume
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteDiagonalReflectionPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.InfiniteVolumeLinkCrossing

/-!
# Reflection-positive states from completed free-boundary limits

This module constructs the neutral `Gauge.ReflectionPositiveState` interface
from the completed-box thermodynamic-limit hypothesis.  The conclusions do
not use a cluster expansion or a strong-coupling radius: only convergence of
the completed boxes and nonnegative Wilson coupling enter.

The completed link box elongated in `nu` is site-symmetric in every other
coordinate and diagonal-symmetric in any two coordinates different from
`nu`.  This is why the limit hypothesis asks for the same limit in every
elongation direction and why the adapter assumes `3 <= d`.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

local instance gluelumpLimitAdapterDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- A link box elongated in `nu` is invariant under a different coordinate
reflection through the origin. -/
theorem siteReflection_mem_linkSymmetricBox_iff_of_ne
    (n : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) (x : Site d) :
    siteReflection tau 0 x ∈ (linkSymmetricBox d n nu).sites ↔
      x ∈ (linkSymmetricBox d n nu).sites := by
  simp only [mem_linkSymmetricBox_sites]
  constructor
  · rintro ⟨hl, hu, hrest⟩
    have hnuCoord : siteReflection tau 0 x nu = x nu := by
      simp [siteReflection_apply_ne hnu]
    rw [hnuCoord] at hl hu
    refine ⟨hl, hu, fun i hi => ?_⟩
    by_cases hit : i = tau
    · subst i
      have ht := hrest tau hnu.symm
      simp only [siteReflection_apply_eq] at ht
      omega
    · simpa [siteReflection_apply_ne hit] using hrest i hi
  · rintro ⟨hl, hu, hrest⟩
    have hnuCoord : siteReflection tau 0 x nu = x nu := by
      simp [siteReflection_apply_ne hnu]
    refine ⟨by simpa [hnuCoord] using hl, by simpa [hnuCoord] using hu,
      fun i hi => ?_⟩
    by_cases hit : i = tau
    · subst i
      have ht := hrest tau hnu.symm
      simp only [siteReflection_apply_eq]
      omega
    · simpa [siteReflection_apply_ne hit] using hrest i hi

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem siteReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
    (n : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) (e : PositiveEdge d) :
    e.siteReflect tau 0 ∈ (linkSymmetricBox d n nu).positiveEdges ↔
      e ∈ (linkSymmetricBox d n nu).positiveEdges := by
  rw [Box.mem_positiveEdges, Box.mem_positiveEdges]
  change ((e.siteReflect tau 0).source ∈ (linkSymmetricBox d n nu).sites ∧
      (e.siteReflect tau 0).target ∈ (linkSymmetricBox d n nu).sites) ↔
    (e.source ∈ (linkSymmetricBox d n nu).sites ∧
      e.target ∈ (linkSymmetricBox d n nu).sites)
  rcases Gauge.FiniteSpecification.siteReflect_endpoints tau 0 e with h | h <;>
    rw [h.1, h.2, siteReflection_mem_linkSymmetricBox_iff_of_ne n hnu,
      siteReflection_mem_linkSymmetricBox_iff_of_ne n hnu]
  exact and_comm

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem siteReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne
    (n : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) (p : Plaquette d) :
    p.siteReflect tau 0 ∈ linkSymmetricActivePlaquettes d n nu ↔
      p ∈ linkSymmetricActivePlaquettes d n nu := by
  have forward : ∀ q : Plaquette d,
      q ∈ linkSymmetricActivePlaquettes d n nu →
        q.siteReflect tau 0 ∈ linkSymmetricActivePlaquettes d n nu := by
    intro q
    simp only [linkSymmetricActivePlaquettes, Finset.mem_biUnion]
    rintro ⟨e, hebox, heq⟩
    refine ⟨e.siteReflect tau 0, ?_, ?_⟩
    · rw [siteReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne n hnu]
      exact hebox
    · rw [mem_incidentPlaquettes_iff_mem_boundary] at heq ⊢
      exact Gauge.FiniteSpecification.siteReflect_mem_plaquette_boundary_of_mem
        tau 0 e q heq
  constructor
  · intro hp
    have href := forward (p.siteReflect tau 0) hp
    rw [Plaquette.siteReflect_siteReflect] at href
    exact href
  · exact forward p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- The completed box elongated transversely to `tau` has exact site
reflection symmetry. -/
theorem linkSymmetricSpecification_siteSymmetric_of_ne
    (n : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) :
    (linkSymmetricSpecification G d n nu).SiteSymmetric tau 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have forward : ∀ a : PositiveEdge d,
        a ∈ (linkSymmetricSpecification G d n nu).dynamicEdges →
          a.siteReflect tau 0 ∈
            (linkSymmetricSpecification G d n nu).dynamicEdges := by
      intro a ha
      rw [linkSymmetricSpecification, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl
          ((siteReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
            n hnu a).mpr ha)
      · right
        rw [Finset.mem_biUnion] at ha ⊢
        obtain ⟨p, hp, hap⟩ := ha
        refine ⟨p.siteReflect tau 0,
          (siteReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne
            n hnu p).mpr hp, ?_⟩
        exact Gauge.FiniteSpecification.siteReflect_mem_plaquette_boundary_of_mem
          tau 0 a p hap
    constructor
    · exact forward e
    · intro he
      have href := forward (e.siteReflect tau 0) he
      simpa using href
  · intro p
    exact (siteReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne n hnu p).symm
  · funext e
    simp [siteReflectConfiguration, linkSymmetricSpecification]

/-- Finite completed boxes are site-reflection positive in every coordinate
transverse to their elongation. -/
theorem linkSymmetricGibbsSequence_siteReflectionPositive_of_ne
    (Phi : RealPlaquettePotential G) (beta : ℝ) (n : ℕ)
    {nu tau : Fin d} (hnu : nu ≠ tau) :
    Gauge.MeasureSiteReflectionPositive
      (linkSymmetricGibbsSequence Phi beta nu n : Measure (Configuration d G))
      tau 0 := by
  intro F hF
  let Lambda := linkSymmetricSpecification G d n nu
  have hfinite := Lambda.siteReflectionPositive_gibbsMeasure tau 0
    (linkSymmetricSpecification_siteSymmetric_of_ne n hnu) Phi beta F hF
  change Complex.im (localExpectation
      (fullGibbsProbability Lambda Phi beta)
        (F.siteReflectionProduct tau 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Lambda Phi beta)
        (F.siteReflectionProduct tau 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Finite completed boxes satisfy site-reflection Cauchy--Schwarz in every
coordinate transverse to their elongation. -/
theorem linkSymmetricGibbsSequence_siteReflectionCauchySchwarz_of_ne
    (Phi : RealPlaquettePotential G) (beta : ℝ) (n : ℕ)
    {nu tau : Fin d} (hnu : nu ≠ tau) :
    Gauge.MeasureSiteReflectionCauchySchwarz
      (linkSymmetricGibbsSequence Phi beta nu n : Measure (Configuration d G))
      tau 0 := by
  intro F H hF hH
  let Lambda := linkSymmetricSpecification G d n nu
  have hfinite :=
    Lambda.normSq_integral_gibbsMeasure_siteReflectionProduct_le tau 0
      (linkSymmetricSpecification_siteSymmetric_of_ne n hnu)
      Phi beta F H hF hH
  unfold Gauge.measureSiteReflectionPairing
  change Complex.normSq (localExpectation
      (fullGibbsProbability Lambda Phi beta)
        (F.siteReflectionProduct tau 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Lambda Phi beta)
        (F.siteReflectionProduct tau 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Lambda Phi beta)
        (H.siteReflectionProduct tau 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- A transverse completed box has site-reflection invariant expectations. -/
theorem linkSymmetricGibbsSequence_integral_siteReflectionPullback_of_ne
    (Phi : RealPlaquettePotential G) (beta : ℝ) (n : ℕ)
    {nu tau : Fin d} (hnu : nu ≠ tau) (F : LocalObservable d G) :
    localExpectation (linkSymmetricGibbsSequence Phi beta nu n)
        (F.siteReflectionPullback tau 0) =
      localExpectation (linkSymmetricGibbsSequence Phi beta nu n) F := by
  let Lambda := linkSymmetricSpecification G d n nu
  simp only [linkSymmetricGibbsSequence, localExpectation_fullGibbsProbability]
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  simp only [LocalObservable.siteReflectionPullback_apply]
  change (∫ V, F (siteReflectConfiguration tau 0 (Lambda.evaluate V))
      ∂Gauge.FiniteVolume.gibbsMeasure Lambda Phi beta) =
    ∫ V, F (Lambda.evaluate V)
      ∂Gauge.FiniteVolume.gibbsMeasure Lambda Phi beta
  exact Lambda.integral_gibbsMeasure_siteReflectConfiguration_eq tau 0
    (linkSymmetricSpecification_siteSymmetric_of_ne n hnu) Phi beta F

/-- Site reflection positivity at the origin passes from a transverse
completed-box exhaustion to an arbitrary limit satisfying the hypothesis. -/
theorem IsTranslationInvariantFreeBoundaryLimit.siteReflectionPositive_zero
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    {nu tau : Fin d} (hnu : nu ≠ tau) :
    Gauge.MeasureSiteReflectionPositive
      (mu : Measure (Configuration d G)) tau 0 := by
  intro F hF
  let O := F.siteReflectionProduct tau 0 F
  have hO := h.localLimit nu O
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hO
  have him := Complex.continuous_im.continuousAt.tendsto.comp hO
  have hfinite : ∀ n,
      Complex.im (localExpectation
        (linkSymmetricGibbsSequence Phi beta nu n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence Phi beta nu n) O) := fun n =>
    linkSymmetricGibbsSequence_siteReflectionPositive_of_ne
      Phi beta n hnu F hF
  constructor
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' <| Filter.Eventually.of_forall
        fun n => (hfinite n).1.symm)
  · exact isClosed_Ici.mem_of_tendsto hre
      (Filter.Eventually.of_forall fun n => (hfinite n).2)

/-- Site Cauchy--Schwarz at the origin passes through the same local limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.siteReflectionCauchySchwarz_zero
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    {nu tau : Fin d} (hnu : nu ≠ tau) :
    Gauge.MeasureSiteReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) tau 0 := by
  intro F H hF hH
  let OFH := F.siteReflectionProduct tau 0 H
  let OFF := F.siteReflectionProduct tau 0 F
  let OHH := H.siteReflectionProduct tau 0 H
  have hlhs := Complex.continuous_normSq.continuousAt.tendsto.comp
    (h.localLimit nu OFH)
  have hrhs :=
    (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit nu OFF)).mul
      (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit nu OHH))
  exact le_of_tendsto_of_tendsto hlhs hrhs <|
    Filter.Eventually.of_forall fun n =>
      linkSymmetricGibbsSequence_siteReflectionCauchySchwarz_of_ne
        Phi beta n hnu F H hF hH

/-- The arbitrary completed-box limit is invariant under a coordinate flip
through the origin, using any transverse elongation direction. -/
theorem IsTranslationInvariantFreeBoundaryLimit.integral_siteReflectionPullback
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    {nu tau : Fin d} (hnu : nu ≠ tau) (F : LocalObservable d G) :
    localExpectation mu (F.siteReflectionPullback tau 0) =
      localExpectation mu F := by
  have hleft := h.localLimit nu (F.siteReflectionPullback tau 0)
  have hright := h.localLimit nu F
  have heq : (fun n => localExpectation
      (linkSymmetricGibbsSequence Phi beta nu n)
        (F.siteReflectionPullback tau 0)) =
      fun n => localExpectation
        (linkSymmetricGibbsSequence Phi beta nu n) F := by
    funext n
    exact linkSymmetricGibbsSequence_integral_siteReflectionPullback_of_ne
      Phi beta n hnu F
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- A link box elongated in `nu` is invariant under a diagonal reflection in
two other coordinates. -/
theorem diagonalReflection_mem_linkSymmetricBox_iff_of_ne
    (n : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) (x : Site d) :
    diagonalReflection tau sigma 0 x ∈ (linkSymmetricBox d n nu).sites ↔
      x ∈ (linkSymmetricBox d n nu).sites := by
  simp only [mem_linkSymmetricBox_sites]
  have hnuCoord : diagonalReflection tau sigma 0 x nu = x nu :=
    diagonalReflection_apply_other hnt hns 0 x
  constructor
  · rintro ⟨hl, hu, hrest⟩
    rw [hnuCoord] at hl hu
    refine ⟨hl, hu, fun i hi => ?_⟩
    by_cases hit : i = tau
    · subst i
      simpa [hts] using hrest sigma hns.symm
    · by_cases his : i = sigma
      · subst i
        simpa [hts] using hrest tau hnt.symm
      · simpa [diagonalReflection_apply_other hit his 0 x] using hrest i hi
  · rintro ⟨hl, hu, hrest⟩
    refine ⟨by simpa [hnuCoord] using hl, by simpa [hnuCoord] using hu,
      fun i hi => ?_⟩
    by_cases hit : i = tau
    · subst i
      simpa using hrest sigma hns.symm
    · by_cases his : i = sigma
      · subst i
        simpa [hts] using hrest tau hnt.symm
      · simpa [diagonalReflection_apply_other hit his 0 x] using hrest i hi

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem diagonalReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
    (n : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) (e : PositiveEdge d) :
    e.diagonalReflect tau sigma 0 ∈
        (linkSymmetricBox d n nu).positiveEdges ↔
      e ∈ (linkSymmetricBox d n nu).positiveEdges := by
  rw [Box.mem_positiveEdges, Box.mem_positiveEdges]
  change ((e.diagonalReflect tau sigma 0).source ∈
      (linkSymmetricBox d n nu).sites ∧
      (e.diagonalReflect tau sigma 0).target ∈
        (linkSymmetricBox d n nu).sites) ↔
    (e.source ∈ (linkSymmetricBox d n nu).sites ∧
      e.target ∈ (linkSymmetricBox d n nu).sites)
  rw [PositiveEdge.source_diagonalReflect,
    PositiveEdge.target_diagonalReflect hts,
    diagonalReflection_mem_linkSymmetricBox_iff_of_ne n hts hnt hns,
    diagonalReflection_mem_linkSymmetricBox_iff_of_ne n hts hnt hns]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem diagonalReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne
    (n : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) (p : Plaquette d) :
    p.diagonalReflect tau sigma 0 ∈
        linkSymmetricActivePlaquettes d n nu ↔
      p ∈ linkSymmetricActivePlaquettes d n nu := by
  have forward : ∀ q : Plaquette d,
      q ∈ linkSymmetricActivePlaquettes d n nu →
        q.diagonalReflect tau sigma 0 ∈
          linkSymmetricActivePlaquettes d n nu := by
    intro q
    simp only [linkSymmetricActivePlaquettes, Finset.mem_biUnion]
    rintro ⟨e, hebox, heq⟩
    refine ⟨e.diagonalReflect tau sigma 0, ?_, ?_⟩
    · rw [diagonalReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
        n hts hnt hns]
      exact hebox
    · rw [mem_incidentPlaquettes_iff_mem_boundary] at heq ⊢
      exact
        Gauge.FiniteSpecification.diagonalReflect_mem_plaquette_boundary_of_mem
          hts 0 e q heq
  constructor
  · intro hp
    have href := forward (p.diagonalReflect tau sigma 0) hp
    rw [Plaquette.diagonalReflect_diagonalReflect hts] at href
    exact href
  · exact forward p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- The completed box elongated in a third coordinate has exact diagonal
reflection symmetry through the origin. -/
theorem linkSymmetricSpecification_diagonalSymmetric_of_ne
    (n : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    (linkSymmetricSpecification G d n nu).DiagonalSymmetric tau sigma 0 := by
  refine ⟨hts, ?_, ?_, ?_⟩
  · intro e
    have forward : ∀ a : PositiveEdge d,
        a ∈ (linkSymmetricSpecification G d n nu).dynamicEdges →
          a.diagonalReflect tau sigma 0 ∈
            (linkSymmetricSpecification G d n nu).dynamicEdges := by
      intro a ha
      rw [linkSymmetricSpecification, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl
          ((diagonalReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
            n hts hnt hns a).mpr ha)
      · right
        rw [Finset.mem_biUnion] at ha ⊢
        obtain ⟨p, hp, hap⟩ := ha
        refine ⟨p.diagonalReflect tau sigma 0,
          (diagonalReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne
            n hts hnt hns p).mpr hp, ?_⟩
        exact
          Gauge.FiniteSpecification.diagonalReflect_mem_plaquette_boundary_of_mem
            hts 0 a p hap
    constructor
    · exact forward e
    · intro he
      have href := forward (e.diagonalReflect tau sigma 0) he
      simpa [PositiveEdge.diagonalReflect_diagonalReflect hts] using href
  · intro p
    exact (diagonalReflect_mem_linkSymmetricActivePlaquettes_iff_of_ne
      n hts hnt hns p).symm
  · funext e
    simp [diagonalReflectConfiguration, linkSymmetricSpecification]

/-- Diagonal RP for a completed box elongated in a third coordinate. -/
theorem linkSymmetricGibbsSequence_diagonalReflectionPositive_of_ne
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta) (n : ℕ)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionPositive
      (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n :
        Measure (Configuration d G)) tau sigma 0 := by
  intro _ F hF
  let Lambda := linkSymmetricSpecification G d n nu
  have hfinite := Lambda.diagonalReflectionPositive_gibbsMeasure tau sigma 0
    (linkSymmetricSpecification_diagonalSymmetric_of_ne n hts hnt hns)
    rho hbeta F hF
  change Complex.im (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (F.diagonalReflectionProduct tau sigma 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (F.diagonalReflectionProduct tau sigma 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Diagonal Cauchy--Schwarz for the same transverse completed box. -/
theorem linkSymmetricGibbsSequence_diagonalReflectionCauchySchwarz_of_ne
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta) (n : ℕ)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionCauchySchwarz
      (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n :
        Measure (Configuration d G)) tau sigma 0 := by
  intro _ F H hF hH
  let Lambda := linkSymmetricSpecification G d n nu
  have hfinite :=
    Lambda.normSq_integral_gibbsMeasure_diagonalReflectionProduct_le
      tau sigma 0
      (linkSymmetricSpecification_diagonalSymmetric_of_ne n hts hnt hns)
      rho hbeta F H hF hH
  unfold Gauge.measureDiagonalReflectionPairing
  change Complex.normSq (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (F.diagonalReflectionProduct tau sigma 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (F.diagonalReflectionProduct tau sigma 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (H.diagonalReflectionProduct tau sigma 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Hermitian symmetry of the diagonal pairing for the transverse box. -/
theorem linkSymmetricGibbsSequence_diagonalReflectionHermitian_of_ne
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    (beta : ℝ) (n : ℕ)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionHermitian
      (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n :
        Measure (Configuration d G)) tau sigma 0 := by
  intro _ F H hF hH
  let Lambda := linkSymmetricSpecification G d n nu
  have hfinite :=
    Lambda.integral_gibbsMeasure_diagonalReflectionProduct_conj_symm
      tau sigma 0
      (linkSymmetricSpecification_diagonalSymmetric_of_ne n hts hnt hns)
      rho beta F H hF hH
  unfold Gauge.measureDiagonalReflectionPairing
  change star (localExpectation
      (fullGibbsProbability Lambda rho.wilsonPotential beta)
        (H.diagonalReflectionProduct tau sigma 0 F)) =
    localExpectation (fullGibbsProbability Lambda rho.wilsonPotential beta)
      (F.diagonalReflectionProduct tau sigma 0 H)
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- A completed box elongated in a coordinate transverse to `tau` and
`sigma` is invariant under swapping those two coordinates.  This is the
finite-volume input used to reorient the final rectangle without imposing a
coordinate-permutation hypothesis on the limiting state. -/
theorem linkSymmetricGibbsSequence_integral_diagonalReflectionPullback_of_ne
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    (beta : ℝ) (n : ℕ)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma)
    (F : LocalObservable d G) :
    localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n)
        (F.diagonalReflectionPullback tau sigma 0) =
      localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) F := by
  let Lambda := linkSymmetricSpecification G d n nu
  simp only [linkSymmetricGibbsSequence,
    localExpectation_fullGibbsProbability]
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  simp only [LocalObservable.diagonalReflectionPullback_apply]
  change (∫ V, F (diagonalReflectConfiguration tau sigma 0
      (Lambda.evaluate V)) ∂Gauge.FiniteVolume.gibbsMeasure Lambda
        rho.wilsonPotential beta) =
    ∫ V, F (Lambda.evaluate V) ∂Gauge.FiniteVolume.gibbsMeasure Lambda
      rho.wilsonPotential beta
  exact Lambda.integral_gibbsMeasure_diagonalReflectConfiguration tau sigma 0
    (linkSymmetricSpecification_diagonalSymmetric_of_ne n hts hnt hns)
    rho beta F

/-- Coordinate-swap invariance passes to every common local limit of the
completed reflection boxes.  At offset zero, diagonal reflection is exactly
the transposition of `tau` and `sigma`. -/
theorem IsTranslationInvariantFreeBoundaryLimit.localExpectation_diagonalReflectionPullback_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma)
    (F : LocalObservable d G) :
    localExpectation mu (F.diagonalReflectionPullback tau sigma 0) =
      localExpectation mu F := by
  have hleft := h.localLimit nu
    (F.diagonalReflectionPullback tau sigma 0)
  have hright := h.localLimit nu F
  have heq :
      (fun n => localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n)
          (F.diagonalReflectionPullback tau sigma 0)) =
        fun n => localExpectation
          (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) F := by
    funext n
    exact
      linkSymmetricGibbsSequence_integral_diagonalReflectionPullback_of_ne
        rho beta n hts hnt hns F
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Dimension at least three supplies the transverse exhaustion coordinate
automatically, exposing coordinate-swap invariance in the form used by the
public rectangle transport layer. -/
theorem IsTranslationInvariantFreeBoundaryLimit.localExpectation_coordinateSwap
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    (hd : 3 ≤ d) {tau sigma : Fin d} (hts : tau ≠ sigma)
    (F : LocalObservable d G) :
    localExpectation mu (F.diagonalReflectionPullback tau sigma 0) =
      localExpectation mu F := by
  obtain ⟨nu, hnt, hns⟩ :=
    Fin.exists_ne_and_ne_of_two_lt tau sigma (by omega : 2 < d)
  exact h.localExpectation_diagonalReflectionPullback_zero
    rho hts hnt hns F

/-- Diagonal RP at the origin passes through a transverse completed-box
local limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.diagonalReflectionPositive_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionPositive
      (mu : Measure (Configuration d G)) tau sigma 0 := by
  intro _ F hF
  let O := F.diagonalReflectionProduct tau sigma 0 F
  have hO := h.localLimit nu O
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hO
  have him := Complex.continuous_im.continuousAt.tendsto.comp hO
  have hfinite : ∀ n,
      Complex.im (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) O) :=
    fun n => linkSymmetricGibbsSequence_diagonalReflectionPositive_of_ne
      rho hbeta n hts hnt hns hts F hF
  constructor
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' <| Filter.Eventually.of_forall
        fun n => (hfinite n).1.symm)
  · exact isClosed_Ici.mem_of_tendsto hre
      (Filter.Eventually.of_forall fun n => (hfinite n).2)

/-- Diagonal Cauchy--Schwarz passes through the same local limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.diagonalReflectionCauchySchwarz_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) tau sigma 0 := by
  intro _ F H hF hH
  let OFH := F.diagonalReflectionProduct tau sigma 0 H
  let OFF := F.diagonalReflectionProduct tau sigma 0 F
  let OHH := H.diagonalReflectionProduct tau sigma 0 H
  have hlhs := Complex.continuous_normSq.continuousAt.tendsto.comp
    (h.localLimit nu OFH)
  have hrhs :=
    (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit nu OFF)).mul
      (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit nu OHH))
  exact le_of_tendsto_of_tendsto hlhs hrhs <|
    Filter.Eventually.of_forall fun n =>
      linkSymmetricGibbsSequence_diagonalReflectionCauchySchwarz_of_ne
        rho hbeta n hts hnt hns hts F H hF hH

/-- Diagonal Hermitian symmetry passes through the same local limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.diagonalReflectionHermitian_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    Gauge.MeasureDiagonalReflectionHermitian
      (mu : Measure (Configuration d G)) tau sigma 0 := by
  intro _ F H hF hH
  let OHF := H.diagonalReflectionProduct tau sigma 0 F
  let OFH := F.diagonalReflectionProduct tau sigma 0 H
  have hleft := continuous_star.continuousAt.tendsto.comp (h.localLimit nu OHF)
  have hright := h.localLimit nu OFH
  have heq : (fun n => star (localExpectation
      (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) OHF)) =
      fun n => localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) OFH := by
    funext n
    exact linkSymmetricGibbsSequence_diagonalReflectionHermitian_of_ne
      rho beta n hts hnt hns hts F H hF hH
  have hleft' : Tendsto (fun n => star (localExpectation
      (linkSymmetricGibbsSequence rho.wilsonPotential beta nu n) OHF)) atTop
      (nhds (star (localExpectation mu OHF))) := by
    simpa only [Function.comp_apply] using hleft
  rw [heq] at hleft'
  unfold Gauge.measureDiagonalReflectionPairing
  exact tendsto_nhds_unique hleft' hright

/-- Ordinary gauge-invariant link RP at the plane `1/2` passes directly
through the completed link-box limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.linkReflectionPositive_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu) (tau : Fin d) :
    Gauge.MeasureLinkReflectionPositive
      (mu : Measure (Configuration d G)) tau 0 := by
  intro F hFhalf hFgauge
  let O := F.linkReflectionProduct tau 0 F
  have hO := h.localLimit tau O
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hO
  have him := Complex.continuous_im.continuousAt.tendsto.comp hO
  have hsupport := support_subset_linkSymmetricSpecification_eventually tau F
  have hfinite : ∀ᶠ n in atTop,
      Complex.im (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) O) :=
    hsupport.mono fun n hn =>
      linkSymmetricGibbsSequence_reflectionPositive_of_support
        rho hbeta n tau F hFhalf hFgauge hn
  constructor
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' <| hfinite.mono fun _ hn => hn.1.symm)
  · exact isClosed_Ici.mem_of_tendsto hre (hfinite.mono fun _ hn => hn.2)

/-- Ordinary link Cauchy--Schwarz at `1/2` passes through the same limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.linkReflectionCauchySchwarz_zero
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu) (tau : Fin d) :
    Gauge.MeasureLinkReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) tau 0 := by
  intro F H hFhalf hHhalf hFgauge hHgauge
  let OFH := F.linkReflectionProduct tau 0 H
  let OFF := F.linkReflectionProduct tau 0 F
  let OHH := H.linkReflectionProduct tau 0 H
  have hlhs := Complex.continuous_normSq.continuousAt.tendsto.comp
    (h.localLimit tau OFH)
  have hrhs :=
    (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit tau OFF)).mul
      (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit tau OHH))
  have hsupportF := support_subset_linkSymmetricSpecification_eventually tau F
  have hsupportH := support_subset_linkSymmetricSpecification_eventually tau H
  exact le_of_tendsto_of_tendsto hlhs hrhs <| by
    filter_upwards [hsupportF, hsupportH] with n hFn hHn
    exact linkSymmetricGibbsSequence_reflectionCauchySchwarz_of_support
      rho hbeta n tau F H hFhalf hHhalf hFgauge hHgauge hFn hHn

/-- A finite Gram-family crossing norm square has a real nonnegative
expectation in every completed-free-boundary limit.  The half families may
depend on the finite box and need not be gauge invariant themselves. -/
theorem IsTranslationInvariantFreeBoundaryLimit.linkCrossingFamilyPositive
    {ι : Type*} [Fintype ι]
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    (tau : Fin d) (O : LocalObservable d G)
    (hpair : EventuallyLinkCrossingFamilyNormSquare (ι := ι) tau O) :
    Complex.im (localExpectation mu O) = 0 ∧
      0 ≤ Complex.re (localExpectation mu O) := by
  have hO := h.localLimit tau O
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hO
  have him := Complex.continuous_im.continuousAt.tendsto.comp hO
  have hfinite : ∀ᶠ n in atTop,
      Complex.im (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) O) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, hF⟩ := hn
    let Lambda := linkSymmetricSpecification G d n tau
    have hfinite := Lambda.linkCrossingFamilyReflectionPositive_gibbsMeasure
      tau 0 (linkSymmetricSpecification_linkSymmetric n tau)
      (linkSymmetricSpecification_plaquetteClosed n tau)
      rho hbeta O F hF
    change Complex.im (localExpectation
        (fullGibbsProbability Lambda rho.wilsonPotential beta) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (fullGibbsProbability Lambda rho.wilsonPotential beta) O)
    rw [localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  constructor
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' <| hfinite.mono fun _ hn => hn.1.symm)
  · exact isClosed_Ici.mem_of_tendsto hre (hfinite.mono fun _ hn => hn.2)

/-- Cauchy--Schwarz for a mixed finite Gram-family crossing certificate in
an arbitrary completed-free-boundary limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.linkCrossingFamilyCauchySchwarz
    {ι : Type*} [Fintype ι]
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    (tau : Fin d) (OFH OFF OHH : LocalObservable d G)
    (hpair : EventuallyLinkCrossingFamilyCauchySchwarz (ι := ι)
      tau OFH OFF OHH) :
    Complex.normSq (localExpectation mu OFH) ≤
      Complex.re (localExpectation mu OFF) *
        Complex.re (localExpectation mu OHH) := by
  have hlhs := Complex.continuous_normSq.continuousAt.tendsto.comp
    (h.localLimit tau OFH)
  have hrhs :=
    (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit tau OFF)).mul
      (Complex.continuous_re.continuousAt.tendsto.comp (h.localLimit tau OHH))
  have hfinite : ∀ᶠ n in atTop,
      Complex.normSq (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) OFH) ≤
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) OFF) *
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence rho.wilsonPotential beta tau n) OHH) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, H, hFH, hFF, hHH⟩ := hn
    let Lambda := linkSymmetricSpecification G d n tau
    have hfinite :=
      Lambda.normSq_integral_gibbsMeasure_crossingFamilyPairing_le
        tau 0 (linkSymmetricSpecification_linkSymmetric n tau)
        (linkSymmetricSpecification_plaquetteClosed n tau)
        rho hbeta OFH OFF OHH F H hFH hFF hHH
    change Complex.normSq (localExpectation
        (fullGibbsProbability Lambda rho.wilsonPotential beta) OFH) ≤
      Complex.re (localExpectation
        (fullGibbsProbability Lambda rho.wilsonPotential beta) OFF) *
      Complex.re (localExpectation
        (fullGibbsProbability Lambda rho.wilsonPotential beta) OHH)
    rw [localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  exact le_of_tendsto_of_tendsto hlhs hrhs hfinite

/-- A completed-free-boundary limit is invariant under every coordinate
reflection through the origin.  A transverse elongation direction is chosen
for each reflection. -/
theorem IsTranslationInvariantFreeBoundaryLimit.coordinateReflectionInvariant
    {Phi : RealPlaquettePotential G} {beta : ℝ}
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit Phi beta mu)
    (hd : 3 ≤ d) :
    Gauge.IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)) := by
  intro tau
  obtain ⟨nu, hnu, _⟩ :=
    Fin.exists_ne_and_ne_of_two_lt tau tau (by omega : 2 < d)
  have hreflect :=
    (continuous_siteReflectConfiguration (G := G) tau 0).measurable
  letI : IsProbabilityMeasure
      (Measure.map (siteReflectConfiguration (G := G) tau 0)
        (mu : Measure (Configuration d G))) :=
    Measure.isProbabilityMeasure_map hreflect.aemeasurable
  apply measure_eq_of_integral_localObservable_eq
  intro F
  rw [MeasureTheory.integral_map hreflect.aemeasurable
    F.toContinuousMap.continuous.aestronglyMeasurable]
  simpa only [LocalObservable.siteReflectionPullback_apply, localExpectation] using
    h.integral_siteReflectionPullback hnu F

/-- The completed-free-boundary hypothesis at nonnegative Wilson coupling
implements the full neutral reflection-positive-state interface.

The coupling restriction is only the usual positivity restriction for link
and diagonal Wilson reflection; site reflection and all Hermitian identities
hold without it. -/
theorem IsTranslationInvariantFreeBoundaryLimit.reflectionPositiveState
    {nrho : ℕ} (rho : Wilson.ContinuousUnitaryRepData G nrho)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariantFreeBoundaryLimit
      rho.wilsonPotential beta mu)
    (hd : 3 ≤ d) : Gauge.ReflectionPositiveState mu := by
  have htrans : Gauge.IsTranslationInvariant
      (mu : Measure (Configuration d G)) := h.translationInvariant
  have hcoord : Gauge.IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)) :=
    h.coordinateReflectionInvariant hd
  have hsitePos : ∀ tau k,
      Gauge.MeasureSiteReflectionPositive
        (mu : Measure (Configuration d G)) tau k := by
    intro tau k
    obtain ⟨nu, hnu, _⟩ :=
      Fin.exists_ne_and_ne_of_two_lt tau tau (by omega : 2 < d)
    exact Gauge.MeasureSiteReflectionPositive.all_planes htrans tau
      (h.siteReflectionPositive_zero hnu) k
  have hsiteCS : ∀ tau k,
      Gauge.MeasureSiteReflectionCauchySchwarz
        (mu : Measure (Configuration d G)) tau k := by
    intro tau k
    obtain ⟨nu, hnu, _⟩ :=
      Fin.exists_ne_and_ne_of_two_lt tau tau (by omega : 2 < d)
    exact Gauge.MeasureSiteReflectionCauchySchwarz.all_planes htrans tau
      (h.siteReflectionCauchySchwarz_zero hnu) k
  have hlinkPos : ∀ tau k,
      Gauge.MeasureLinkReflectionPositive
        (mu : Measure (Configuration d G)) tau k := by
    intro tau k
    exact Gauge.MeasureLinkReflectionPositive.all_planes htrans tau
      (h.linkReflectionPositive_zero rho hbeta tau) k
  have hlinkCS : ∀ tau k,
      Gauge.MeasureLinkReflectionCauchySchwarz
        (mu : Measure (Configuration d G)) tau k := by
    intro tau k
    exact Gauge.MeasureLinkReflectionCauchySchwarz.all_planes htrans tau
      (h.linkReflectionCauchySchwarz_zero rho hbeta tau) k
  have hdiagPos : ∀ tau sigma k,
      Gauge.MeasureDiagonalReflectionPositive
        (mu : Measure (Configuration d G)) tau sigma k := by
    intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · obtain ⟨nu, hnt, hns⟩ :=
        Fin.exists_ne_and_ne_of_two_lt tau sigma (by omega : 2 < d)
      exact Gauge.MeasureDiagonalReflectionPositive.all_planes htrans hts
        (h.diagonalReflectionPositive_zero rho hbeta hts hnt hns) k
  have hdiagCS : ∀ tau sigma k,
      Gauge.MeasureDiagonalReflectionCauchySchwarz
        (mu : Measure (Configuration d G)) tau sigma k := by
    intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · obtain ⟨nu, hnt, hns⟩ :=
        Fin.exists_ne_and_ne_of_two_lt tau sigma (by omega : 2 < d)
      exact Gauge.MeasureDiagonalReflectionCauchySchwarz.all_planes htrans hts
        (h.diagonalReflectionCauchySchwarz_zero rho hbeta hts hnt hns) k
  have hdiagHerm : ∀ tau sigma k,
      Gauge.MeasureDiagonalReflectionHermitian
        (mu : Measure (Configuration d G)) tau sigma k := by
    intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · obtain ⟨nu, hnt, hns⟩ :=
        Fin.exists_ne_and_ne_of_two_lt tau sigma (by omega : 2 < d)
      exact Gauge.MeasureDiagonalReflectionHermitian.all_planes htrans hts
        (h.diagonalReflectionHermitian_zero rho hts hnt hns) k
  refine
    { translationInvariant := htrans
      coordinateReflectionInvariant := hcoord
      sitePositive := hsitePos
      siteCauchySchwarz := hsiteCS
      linkPositive := hlinkPos
      linkCauchySchwarz := hlinkCS
      diagonalPositive := hdiagPos
      diagonalCauchySchwarz := hdiagCS
      diagonalHermitian := hdiagHerm
      antiDiagonalPositive := ?_
      antiDiagonalCauchySchwarz := ?_
      antiDiagonalHermitian := ?_ }
  · intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · exact Gauge.MeasureAntiDiagonalReflectionPositive.of_diagonal
        hcoord hts k (hdiagPos tau sigma k)
  · intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · exact Gauge.MeasureAntiDiagonalReflectionCauchySchwarz.of_diagonal
        hcoord hts k (hdiagCS tau sigma k)
  · intro tau sigma k
    by_cases hts : tau = sigma
    · subst sigma
      intro hne
      exact (hne rfl).elim
    · exact Gauge.MeasureAntiDiagonalReflectionHermitian.of_diagonal
        hcoord hts k (hdiagHerm tau sigma k)

end

end YangMills.StrongCoupling
