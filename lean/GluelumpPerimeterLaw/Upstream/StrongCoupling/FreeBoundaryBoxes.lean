/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteLinkReflectionPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteDiagonalReflectionPositivity

/-!
# Internal-edge free-boundary reflection boxes

The dynamic variables are precisely the edges contained in the site box.
Only plaquettes with all four edges in that box enter the action. Both
ordered axis labels are retained, as in the paper's oriented plaquette sum.
The geometric reflection lemmas below are extracted from the existing
completed-box adapter; the finite reflection APIs apply to this ordinary
free-boundary specification directly.
-/

open Filter MeasureTheory
namespace YangMills.StrongCoupling
open Gauge Lattice.Cubic
noncomputable section
local instance freeBoundaryDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _
variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Incident plaquettes whose complete boundary is internal. -/
def freeBoundaryActivePlaquettes (d radius : ℕ) (tau : Fin d) : Finset (Plaquette d) :=
  (linkSymmetricActivePlaquettes d radius tau).filter fun p =>
    p.boundary.edgeSupport ⊆ (linkSymmetricBox d radius tau).positiveEdges

/-- The paper's ordinary free-boundary specification. -/
def freeBoundarySpecification (G : Type*) [Group G]
    (d radius : ℕ) (tau : Fin d) : FiniteSpecification d G where
  dynamicEdges := (linkSymmetricBox d radius tau).positiveEdges
  activePlaquettes := freeBoundaryActivePlaquettes d radius tau
  exterior := 1

@[simp] theorem freeBoundarySpecification_dynamicEdges
    (radius : ℕ) (tau : Fin d) :
    (freeBoundarySpecification G d radius tau).dynamicEdges =
      (linkSymmetricBox d radius tau).positiveEdges := rfl

theorem freeBoundarySpecification_plaquetteClosed (radius : ℕ) (tau : Fin d) :
    (freeBoundarySpecification G d radius tau).PlaquetteClosed := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- Every contained plaquette is present; the incident-set prefilter
introduces no restriction. -/
theorem mem_freeBoundaryActivePlaquettes_iff (radius : ℕ) (tau : Fin d)
    (p : Plaquette d) :
    p ∈ freeBoundaryActivePlaquettes d radius tau ↔
      p.boundary.edgeSupport ⊆ (linkSymmetricBox d radius tau).positiveEdges := by
  constructor
  · exact fun hp => (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    have hnonempty : p.boundary.edgeSupport.Nonempty := by
      rw [plaquette_boundary_edgeSupport]
      exact ⟨⟨p.base, p.first⟩, by simp⟩
    obtain ⟨e, he⟩ := hnonempty
    exact Finset.mem_biUnion.mpr
      ⟨e, hp he, mem_incidentPlaquettes_of_mem_boundary e p he⟩

/-- Product-Haar Gibbs law at the normalized-potential coupling. -/
def freeBoundaryGibbsSequence (Phi : RealPlaquettePotential G) (beta : ℝ)
    (tau : Fin d) (radius : ℕ) : ProbabilityMeasure (Configuration d G) :=
  fullGibbsProbability (freeBoundarySpecification G d radius tau) Phi beta

/-- Every fixed finite support is eventually internal. -/
theorem support_subset_freeBoundarySpecification_eventually
    (tau : Fin d) (F : LocalObservable d G) :
    ∀ᶠ radius in atTop,
      F.support ⊆ (freeBoundarySpecification G d radius tau).dynamicEdges := by
  obtain ⟨N, hN⟩ := finiteSupport_subset_linkSymmetricBox tau F.support
  exact Filter.eventually_atTop.2 ⟨N, fun radius h =>
    hN.trans (linkSymmetricBox_positiveEdges_mono h tau)⟩

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


/-- Contained plaquettes are preserved by link reflection. -/
theorem linkReflect_mem_freeBoundaryActivePlaquettes_iff
    (radius : ℕ) (tau : Fin d) (p : Plaquette d) :
    p.linkReflect tau 0 ∈ freeBoundaryActivePlaquettes d radius tau ↔
      p ∈ freeBoundaryActivePlaquettes d radius tau := by
  have forward : ∀ p : Plaquette d,
      p ∈ freeBoundaryActivePlaquettes d radius tau →
        p.linkReflect tau 0 ∈ freeBoundaryActivePlaquettes d radius tau := by
    intro p hp
    rw [mem_freeBoundaryActivePlaquettes_iff] at hp ⊢
    intro e he
    have hmem := Gauge.FiniteSpecification.linkReflect_mem_plaquette_boundary_iff
      tau 0 (e.linkReflect tau 0) p
    have he' : e.linkReflect tau 0 ∈ p.boundary.edgeSupport := by
      simpa only [PositiveEdge.linkReflect_linkReflect] using hmem.mp (by simpa using he)
    exact (linkReflect_mem_linkSymmetricBox_positiveEdges_iff radius tau e).mp (by simpa using hp he')
  constructor
  · intro hp
    have h := forward (p.linkReflect tau 0) hp
    simpa only [Plaquette.linkReflect_linkReflect] using h
  · exact forward p

/-- The internal-edge specification has exact link symmetry. -/
theorem freeBoundarySpecification_linkSymmetric (radius : ℕ) (tau : Fin d) :
    (freeBoundarySpecification G d radius tau).LinkSymmetric tau 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact (linkReflect_mem_linkSymmetricBox_positiveEdges_iff radius tau e).symm
  · intro p
    exact (linkReflect_mem_freeBoundaryActivePlaquettes_iff radius tau p).symm
  · funext e
    simp [linkReflectConfiguration, freeBoundarySpecification]

/-- Contained plaquettes are preserved by site reflection. -/
theorem siteReflect_mem_freeBoundaryActivePlaquettes_iff_of_ne
    (radius : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) (p : Plaquette d) :
    p.siteReflect tau 0 ∈ freeBoundaryActivePlaquettes d radius nu ↔
      p ∈ freeBoundaryActivePlaquettes d radius nu := by
  have forward : ∀ p : Plaquette d,
      p ∈ freeBoundaryActivePlaquettes d radius nu →
        p.siteReflect tau 0 ∈ freeBoundaryActivePlaquettes d radius nu := by
    intro p hp
    rw [mem_freeBoundaryActivePlaquettes_iff] at hp ⊢
    intro e he
    have hmem := Gauge.FiniteSpecification.siteReflect_mem_plaquette_boundary_iff
      tau 0 (e.siteReflect tau 0) p
    rw [PositiveEdge.siteReflect_siteReflect] at hmem
    exact (siteReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
      radius hnu e).mp (hp (hmem.mp he))
  constructor
  · intro hp
    have h := forward (p.siteReflect tau 0) hp
    simpa only [Plaquette.siteReflect_siteReflect] using h
  · exact forward p

/-- The internal-edge specification has exact site symmetry. -/
theorem freeBoundarySpecification_siteSymmetric_of_ne (radius : ℕ) {nu tau : Fin d} (hnu : nu ≠ tau) :
    (freeBoundarySpecification G d radius nu).SiteSymmetric tau 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact (siteReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne radius hnu e).symm
  · intro p
    exact (siteReflect_mem_freeBoundaryActivePlaquettes_iff_of_ne radius hnu p).symm
  · funext e
    simp [siteReflectConfiguration, freeBoundarySpecification]

/-- Contained plaquettes are preserved by diagonal reflection. -/
theorem diagonalReflect_mem_freeBoundaryActivePlaquettes_iff_of_ne
    (radius : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) (p : Plaquette d) :
    p.diagonalReflect tau sigma 0 ∈ freeBoundaryActivePlaquettes d radius nu ↔
      p ∈ freeBoundaryActivePlaquettes d radius nu := by
  have forward : ∀ p : Plaquette d,
      p ∈ freeBoundaryActivePlaquettes d radius nu →
        p.diagonalReflect tau sigma 0 ∈ freeBoundaryActivePlaquettes d radius nu := by
    intro p hp
    rw [mem_freeBoundaryActivePlaquettes_iff] at hp ⊢
    intro e he
    have hmem := Gauge.FiniteSpecification.diagonalReflect_mem_plaquette_boundary_iff
      hts 0 (e.diagonalReflect tau sigma 0) p
    rw [PositiveEdge.diagonalReflect_diagonalReflect hts] at hmem
    exact (diagonalReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne
      radius hts hnt hns e).mp (hp (hmem.mp he))
  constructor
  · intro hp
    have h := forward (p.diagonalReflect tau sigma 0) hp
    simpa only [Plaquette.diagonalReflect_diagonalReflect hts] using h
  · exact forward p

/-- The internal-edge specification has exact diagonal symmetry. -/
theorem freeBoundarySpecification_diagonalSymmetric_of_ne (radius : ℕ) {nu tau sigma : Fin d} (hts : tau ≠ sigma)
    (hnt : nu ≠ tau) (hns : nu ≠ sigma) :
    (freeBoundarySpecification G d radius nu).DiagonalSymmetric tau sigma 0 := by
  refine ⟨hts, ?_, ?_, ?_⟩
  · intro e
    exact (diagonalReflect_mem_linkSymmetricBox_positiveEdges_iff_of_ne radius hts hnt hns e).symm
  · intro p
    exact (diagonalReflect_mem_freeBoundaryActivePlaquettes_iff_of_ne radius hts hnt hns p).symm
  · funext e
    simp [diagonalReflectConfiguration, freeBoundarySpecification]

theorem freeBoundaryGibbsSequence_reflectionPositive_of_support
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (τ : Fin d)
    (F : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ 0)
    (hFgauge : Gauge.IsGaugeInvariant F)
    (hFdyn : F.support ⊆
      (freeBoundarySpecification G d n τ).dynamicEdges) :
    Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n)
        (F.linkReflectionProduct τ 0 F)) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n)
          (F.linkReflectionProduct τ 0 F)) := by
  let Λ := freeBoundarySpecification G d n τ
  have hfinite := Λ.linkReflectionPositive_gibbsMeasure τ 0
    (freeBoundarySpecification_linkSymmetric n τ)
    (freeBoundarySpecification_plaquetteClosed n τ)
    ρ hβ F hFhalf hFgauge hFdyn
  change Complex.im (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite


theorem freeBoundaryGibbsSequence_reflectionCauchySchwarz_of_support
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (τ : Fin d)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ 0)
    (hHhalf : H.SupportedInLinkPositiveHalf τ 0)
    (hFgauge : Gauge.IsGaugeInvariant F)
    (hHgauge : Gauge.IsGaugeInvariant H)
    (hFdyn : F.support ⊆
      (freeBoundarySpecification G d n τ).dynamicEdges)
    (hHdyn : H.support ⊆
      (freeBoundarySpecification G d n τ).dynamicEdges) :
    Complex.normSq (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n)
        (F.linkReflectionProduct τ 0 H)) ≤
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n)
          (F.linkReflectionProduct τ 0 F)) *
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n)
          (H.linkReflectionProduct τ 0 H)) := by
  let Λ := freeBoundarySpecification G d n τ
  have hfinite :=
    Λ.normSq_integral_gibbsMeasure_linkReflectionProduct_le τ 0
      (freeBoundarySpecification_linkSymmetric n τ)
      (freeBoundarySpecification_plaquetteClosed n τ)
      ρ hβ F H hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn
  change Complex.normSq (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (H.linkReflectionProduct τ 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite


end
end YangMills.StrongCoupling
