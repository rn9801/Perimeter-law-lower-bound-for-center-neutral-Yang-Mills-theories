/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteLocalKernelBound
import GluelumpPerimeterLaw.OneLink.ConjugationSpanOneLinkFactorization

/-!
# Uniform finite-volume one-link lower bound

This file instantiates the exact endpoint-mode, finite-energy, partition
reordering, and common-remote-factor cancellation chain for the direct
conjugation-span endpoint.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint Propagation
open RepresentationTheory Representation
open scoped BigOperators

noncomputable section

universe u uX

/-! ## A fixed upper bound for feature relabeling cost -/

section FeatureRelabelingCost

variable {X : Type uX} [TopologicalSpace X]
  {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  {N : ℕ} {featureA : A → C(X, ℂ)} {Phi : I → C(X, ℂ)}

/-- The coefficient `l1` norm after feature relabeling is bounded by the
target word count times the original `l1` norm. -/
theorem EndpointConjugateMode.mapFeature_coefficientL1_le
    (mode : EndpointConjugateMode featureA Phi N)
    (featureB : B → C(X, ℂ)) (embed : A → B)
    (hfeature : ∀ a, featureB (embed a) = featureA a) :
    (∑ word : FeatureWord B N,
        ‖(mode.mapFeature featureB embed hfeature).coefficient word‖) ≤
      Fintype.card (FeatureWord B N) *
        ∑ word : FeatureWord A N, ‖mode.coefficient word‖ := by
  classical
  let lifted := mode.mapFeature featureB embed hfeature
  let L : ℝ := ∑ word : FeatureWord A N, ‖mode.coefficient word‖
  have hcoeff (wordB : FeatureWord B N) :
      ‖lifted.coefficient wordB‖ ≤ L := by
    dsimp only [lifted, EndpointConjugateMode.mapFeature,
      HomogeneousFeatureExpansion.mapFeature]
    calc
      ‖∑ wordA : FeatureWord A N,
          if (fun word i ↦ embed (word i)) wordA = wordB then
            mode.coefficient wordA else 0‖ ≤
          ∑ wordA : FeatureWord A N,
            ‖if (fun word i ↦ embed (word i)) wordA = wordB then
              mode.coefficient wordA else 0‖ := norm_sum_le _ _
      _ ≤ L := by
        apply Finset.sum_le_sum
        intro wordA _hwordA
        split <;> simp
  calc
    ∑ wordB : FeatureWord B N, ‖lifted.coefficient wordB‖ ≤
        ∑ _wordB : FeatureWord B N, L :=
      Finset.sum_le_sum fun wordB _hwordB ↦ hcoeff wordB
    _ = Fintype.card (FeatureWord B N) * L := by simp

/-- Relabeling an endpoint mode into a finite feature family has a coarse
cost bounded by the target word count and the source coefficient `l1` norm.
This estimate does not assume injectivity and is therefore stable under
repeated crossing labels. -/
theorem EndpointConjugateMode.mapFeature_extractionCost_le
    (mode : EndpointConjugateMode featureA Phi N)
    (featureB : B → C(X, ℂ)) (embed : A → B)
    (hfeature : ∀ a, featureB (embed a) = featureA a) :
    (mode.mapFeature featureB embed hfeature).extractionCost ≤
      mode.lambdaNormSq *
        (Fintype.card (FeatureWord B N) *
          (∑ word : FeatureWord A N, ‖mode.coefficient word‖) ^ 2) := by
  classical
  let lifted := mode.mapFeature featureB embed hfeature
  let L : ℝ := ∑ word : FeatureWord A N, ‖mode.coefficient word‖
  have hcoeff (wordB : FeatureWord B N) :
      ‖lifted.coefficient wordB‖ ≤ L := by
    dsimp only [lifted, EndpointConjugateMode.mapFeature,
      HomogeneousFeatureExpansion.mapFeature]
    calc
      ‖∑ wordA : FeatureWord A N,
          if (fun word i ↦ embed (word i)) wordA = wordB then
            mode.coefficient wordA else 0‖ ≤
          ∑ wordA : FeatureWord A N,
            ‖if (fun word i ↦ embed (word i)) wordA = wordB then
              mode.coefficient wordA else 0‖ := norm_sum_le _ _
      _ ≤ L := by
        apply Finset.sum_le_sum
        intro wordA _hwordA
        split <;> simp
  have hcoeffSq (wordB : FeatureWord B N) :
      ‖lifted.coefficient wordB‖ ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hcoeff wordB) 2
  have hsum : lifted.coefficientNormSq ≤
      Fintype.card (FeatureWord B N) * L ^ 2 := by
    unfold EndpointConjugateMode.coefficientNormSq
    calc
      ∑ wordB : FeatureWord B N, ‖lifted.coefficient wordB‖ ^ 2 ≤
          ∑ _wordB : FeatureWord B N, L ^ 2 :=
        Finset.sum_le_sum fun wordB _hwordB ↦ hcoeffSq wordB
      _ = Fintype.card (FeatureWord B N) * L ^ 2 := by
        simp
  unfold EndpointConjugateMode.extractionCost
  have hlambda : lifted.lambdaNormSq = mode.lambdaNormSq := by
    rfl
  rw [hlambda]
  exact mul_le_mul_of_nonneg_left hsum
    (by exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

end FeatureRelabelingCost

section MatrixReindexingCost

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  {n N : ℕ} {J K I : Type*} [Fintype J] [Fintype K] [Fintype I]

/-- Coordinate reindexing contributes at most one target-word-count factor
to the coefficient `l1` norm. -/
theorem reindexMatrixEndpointMode_coefficientL1_le
    (sigma : ContinuousUnitaryRepData G n) (e : J ≃ K)
    (Phi : I → C(J → G, ℂ))
    (mode : EndpointConjugateMode (matrixFeature sigma) Phi N) :
    (∑ word : FeatureWord (MatrixFeatureLetter K n) N,
        ‖(reindexMatrixEndpointMode sigma e Phi mode).coefficient word‖) ≤
      Fintype.card (FeatureWord (MatrixFeatureLetter K n) N) *
        ∑ word : FeatureWord (MatrixFeatureLetter J n) N,
          ‖mode.coefficient word‖ := by
  unfold reindexMatrixEndpointMode
  dsimp only
  apply EndpointConjugateMode.mapFeature_coefficientL1_le

end MatrixReindexingCost

/-! ## Fixed direct-endpoint constants -/

section DirectEndpointConstants

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

/-- Haar `L²` mass of the fixed scalar endpoint mode in its physical comb
coordinates. -/
def conjSpanCombScalarMass
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) : ℝ :=
  let mode := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  scalarEndpointMass
    (ProductHaar.measure G (combEndpointCollar (m := m) hd x))
    (endpointScalarPart mode.lambda
      (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i))

theorem conjSpanCombScalarMass_pos
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanCombScalarMass hd sigma rho T hT x := by
  letI : Measure.IsOpenPosMeasure
      (ProductHaar.measure G (combEndpointCollar (m := m) hd x)) := by
    unfold ProductHaar.measure
    infer_instance
  let mode := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  exact endpointModeScalarMass_pos
    (ProductHaar.measure G (combEndpointCollar (m := m) hd x))
    (matrixFeature sigma)
    (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i) mode

/-- A volume-independent upper bound for the endpoint-mode extraction cost
after embedding into all selected crossing labels. -/
def conjSpanCombExtractionBound
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) : ℝ :=
  let mode := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  let labelBound :=
    1 + (4 * d * (combEndpointCollar (m := m) hd x).card) * 2 * n * n
  let wordBound := labelBound ^ (combEndpointDegree (m := m) hd x)
  mode.lambdaNormSq *
    (wordBound *
      (wordBound * ∑ word, ‖mode.coefficient word‖) ^ 2)

theorem conjSpanCombExtractionBound_pos
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanCombExtractionBound hd sigma rho T hT x := by
  let mode := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  have hsum : 0 < ∑ word, ‖mode.coefficient word‖ := by
    obtain ⟨word, hword⟩ := mode.exists_coefficient_ne_zero
    exact Finset.sum_pos' (fun _ _ ↦ norm_nonneg _)
      ⟨word, Finset.mem_univ word, norm_pos_iff.mpr hword⟩
  have hlabel : 0 <
      1 + (4 * d * (combEndpointCollar (m := m) hd x).card) * 2 * n * n := by
    omega
  unfold conjSpanCombExtractionBound
  dsimp only
  exact mul_pos mode.lambdaNormSq_pos
    (mul_pos (Nat.cast_pos.mpr (pow_pos hlabel _))
      (sq_pos_of_pos (mul_pos
        (Nat.cast_pos.mpr (pow_pos hlabel _)) hsum)))

/-- The selected doubled crossing-letter family has a fixed collar-cardinality
bound. -/
theorem card_linkCombEndpointLetter_le
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n) :
    Fintype.card
        ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau k hLambda hclosed sigma).EndpointLetter
          (linkCombSelected (m := m) Lambda tau k hd x)) ≤
      (4 * d * (combEndpointCollar (m := m) hd x).card) * 2 * n * n := by
  have hq := card_linkCombSelectedCrossingLabels_le
    (m := m) Lambda tau k hLambda hclosed hd x sigma
  simpa only [CoordinateCrossingData.EndpointLetter, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, mul_assoc] using
    Nat.mul_le_mul_right (2 * n * n) hq

/-! ## A cost-controlled selected crossing mode -/

/-- Choose one visible crossing plaquette for a selected physical collar
edge.  This choice is used only to embed the fixed endpoint mode; all other
crossing labels remain in the ambient feature family. -/
def linkConjSpanVisibleCrossingLabel
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e)
    (e : CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x)) :
    {q : Lambda.linkCrossPlaquettes tau k //
      linkCombSelected (m := m) Lambda tau k hd x
        ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau k hLambda hclosed sigma).edge q)} := by
  let physical : combEndpointCollar (m := m) hd x := ⟨e.1.1, e.2⟩
  let q := Classical.choose (hvisible physical.1 physical.2)
  refine ⟨q, ?_⟩
  change FiniteSpecification.linkCrossPositiveEdge tau q.1 ∈
    combEndpointCollar (m := m) hd x
  rw [Classical.choose_spec (hvisible physical.1 physical.2)]
  exact physical.2

theorem linkConjSpanVisibleCrossingLabel_edge
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e)
    (e : CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x)) :
    (FiniteSpecification.linkCoordinateCrossingData
      Lambda tau k hLambda hclosed sigma).edge
        (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed hd x
          sigma hvisible e).1 = e.1 := by
  apply Subtype.ext
  change FiniteSpecification.linkCrossPositiveEdge tau
    (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed hd x
      sigma hvisible e).1.1 = e.1.1
  unfold linkConjSpanVisibleCrossingLabel
  simp only
  exact Classical.choose_spec (hvisible e.1.1 e.2)

/-- The exact nonzero endpoint mode embedded using the preceding fixed
visible-label choice. -/
def uniformLinkConjSpanEndpointCrossMode
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    EndpointConjugateMode
      ((FiniteSpecification.linkCoordinateCrossingData
        Lambda tau k hLambda hclosed sigma).endpointFeature
        (linkCombSelected (m := m) Lambda tau k hd x))
      (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
      (combEndpointDegree (m := m) hd x) :=
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
  data.endpointModeOfCollarMode
    (linkCombSelected (m := m) Lambda tau k hd x)
    (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
    (linkConjSpanCollarMode Lambda tau k hd sigma rho T hT x hcollar)
    (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed hd x
      sigma hvisible)
    (linkConjSpanVisibleCrossingLabel_edge Lambda tau k hLambda hclosed hd x
      sigma hvisible)

/-- The cost of the selected crossing mode is bounded by the fixed physical
comb data, uniformly in the finite specification. -/
theorem uniformLinkConjSpanEndpointCrossMode_extractionCost_le
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    (uniformLinkConjSpanEndpointCrossMode Lambda tau k hLambda hclosed hd
      sigma rho T hT x hcollar hvisible).extractionCost ≤
      conjSpanCombExtractionBound hd sigma rho T hT x := by
  classical
  let S := combEndpointCollar (m := m) hd x
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
  let mode₀ := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  let modeC := linkConjSpanCollarMode
    Lambda tau k hd sigma rho T hT x hcollar
  let modeX := uniformLinkConjSpanEndpointCrossMode Lambda tau k hLambda
    hclosed hd sigma rho T hT x hcollar hvisible
  let labelBound := 1 + (4 * d * S.card) * 2 * n * n
  let wordBound := labelBound ^ (combEndpointDegree (m := m) hd x)
  have hcardC : Fintype.card (CollarCoordinate selected) = S.card := by
    simpa [selected, S] using Fintype.card_congr
      (linkCombCollarEquiv Lambda tau k hd x hcollar).symm
  have hletterC :
      Fintype.card (MatrixFeatureLetter (CollarCoordinate selected) n) ≤
        labelBound := by
    have hmatrix :
        Fintype.card (MatrixFeatureLetter (CollarCoordinate selected) n) =
          S.card * 2 * n * n := by
      simp [MatrixFeatureLetter, hcardC, mul_assoc]
    rw [hmatrix]
    dsimp only [labelBound]
    have h4d : 1 ≤ 4 * d := by omega
    have hraw : S.card * 2 * n * n ≤ 4 * d * S.card * 2 * n * n := by
      calc
        S.card * 2 * n * n = 1 * (S.card * 2 * n * n) := by omega
        _ ≤ (4 * d) * (S.card * 2 * n * n) :=
          Nat.mul_le_mul_right (S.card * 2 * n * n) h4d
        _ = 4 * d * S.card * 2 * n * n := by ring
    exact hraw.trans (Nat.le_add_left _ 1)
  have hwordC : Fintype.card
      (FeatureWord (MatrixFeatureLetter (CollarCoordinate selected) n)
        (combEndpointDegree (m := m) hd x)) ≤ wordBound := by
    simpa only [FeatureWord, Fintype.card_fun, Fintype.card_fin, wordBound] using
      pow_le_pow_left' hletterC (combEndpointDegree (m := m) hd x)
  have hletterX : Fintype.card (data.EndpointLetter selected) ≤ labelBound :=
    (card_linkCombEndpointLetter_le (m := m) Lambda tau k hLambda hclosed
      hd x sigma).trans (Nat.le_add_left _ 1)
  have hwordX : Fintype.card
      (FeatureWord (data.EndpointLetter selected)
        (combEndpointDegree (m := m) hd x)) ≤ wordBound := by
    simpa only [FeatureWord, Fintype.card_fun, Fintype.card_fin, wordBound] using
      pow_le_pow_left' hletterX (combEndpointDegree (m := m) hd x)
  have hLC : (∑ word, ‖modeC.coefficient word‖) ≤
      wordBound * ∑ word, ‖mode₀.coefficient word‖ := by
    have hreindex := reindexMatrixEndpointMode_coefficientL1_le sigma
      (linkCombCollarEquiv Lambda tau k hd x hcollar)
      (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i) mode₀
    have hwordCReal :
        (Fintype.card (FeatureWord
          (MatrixFeatureLetter (CollarCoordinate selected) n)
          (combEndpointDegree (m := m) hd x)) : ℝ) ≤ wordBound := by
      exact_mod_cast hwordC
    calc
      (∑ word, ‖modeC.coefficient word‖) ≤
          Fintype.card (FeatureWord
            (MatrixFeatureLetter (CollarCoordinate selected) n)
            (combEndpointDegree (m := m) hd x)) *
            ∑ word, ‖mode₀.coefficient word‖ := by
        simpa [modeC, mode₀, linkConjSpanCollarMode] using hreindex
      _ ≤ wordBound * ∑ word, ‖mode₀.coefficient word‖ :=
        mul_le_mul_of_nonneg_right hwordCReal
          (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hmap := modeC.mapFeature_extractionCost_le
    (data.endpointFeature selected)
    (fun a : MatrixFeatureLetter (CollarCoordinate selected) n ↦
      (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed hd x
        sigma hvisible a.1, a.2.1, a.2.2.1, a.2.2.2))
    (by
      intro a
      ext U
      rcases a with ⟨e, b, i, j⟩
      simp only [CoordinateCrossingData.endpointFeature, matrixFeature]
      have he := linkConjSpanVisibleCrossingLabel_edge
        Lambda tau k hLambda hclosed hd x sigma hvisible e
      have he' :
          (⟨data.edge
              (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed
                hd x sigma hvisible e).1,
            (linkConjSpanVisibleCrossingLabel Lambda tau k hLambda hclosed
              hd x sigma hvisible e).2⟩ : CollarCoordinate selected) = e :=
        Subtype.ext he
      rw [he']
      rfl)
  have hwordXReal :
      (Fintype.card (FeatureWord (data.EndpointLetter selected)
        (combEndpointDegree (m := m) hd x)) : ℝ) ≤ wordBound := by
    exact_mod_cast hwordX
  have hlambda : modeC.lambdaNormSq = mode₀.lambdaNormSq := by
    rfl
  calc
    modeX.extractionCost ≤ modeC.lambdaNormSq *
        (Fintype.card (FeatureWord (data.EndpointLetter selected)
          (combEndpointDegree (m := m) hd x)) *
          (∑ word, ‖modeC.coefficient word‖) ^ 2) := by
      simpa [modeX, uniformLinkConjSpanEndpointCrossMode, data, selected]
        using hmap
    _ ≤ mode₀.lambdaNormSq *
        (wordBound *
          (wordBound * ∑ word, ‖mode₀.coefficient word‖) ^ 2) := by
      rw [hlambda]
      gcongr
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    _ = conjSpanCombExtractionBound hd sigma rho T hT x := by
      rfl

/-- Reindexing the physical comb coordinates into a selected finite-volume
collar preserves the scalar endpoint Haar mass exactly. -/
theorem uniformLinkConjSpanEndpointCrossMode_scalarMass_eq
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    let selected := linkCombSelected (m := m) Lambda tau k hd x
    let mode := uniformLinkConjSpanEndpointCrossMode Lambda tau k hLambda
      hclosed hd sigma rho T hT x hcollar hvisible
    scalarEndpointMass (ProductHaar.measure G (CollarCoordinate selected))
        (endpointScalarPart mode.lambda
          (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)) =
      conjSpanCombScalarMass hd sigma rho T hT x := by
  let S := combEndpointCollar (m := m) hd x
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let e := linkCombCollarEquiv Lambda tau k hd x hcollar
  let mode₀ := conjSpanCombEndpointConjugateMode hd sigma rho T hT x
  let mode := uniformLinkConjSpanEndpointCrossMode Lambda tau k hLambda
    hclosed hd sigma rho T hT x hcollar hvisible
  have hlambda : mode.lambda = mode₀.lambda := by
    rfl
  have hscalar (U : CollarCoordinate selected → G) :
      endpointScalarPart mode.lambda
          (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar) U =
        endpointScalarPart mode₀.lambda
          (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i)
          (ProductHaar.reindex (G := G) e.symm U) := by
    rw [hlambda]
    simp only [endpointScalarPart_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
  unfold conjSpanCombScalarMass scalarEndpointMass
  dsimp only
  rw [show (fun U : CollarCoordinate selected → G ↦
      ‖endpointScalarPart mode.lambda
        (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar) U‖ ^ 2) =
      fun U ↦ ‖endpointScalarPart mode₀.lambda
        (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i)
        (ProductHaar.reindex (G := G) e.symm U)‖ ^ 2 by
    funext U
    rw [hscalar U]]
  simpa only [mode₀] using ProductHaar.integral_reindex (G := G) e.symm
    (fun U ↦ ‖endpointScalarPart mode₀.lambda
      (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i) U‖ ^ 2)

/-! ## The explicit finite-volume-independent constant -/

/-- The direct conjugation-span one-link constant.  Every term depends only
on the coupling, the fixed representation/intertwiner data, and the fixed
physical comb based at `x`; it does not depend on the finite specification. -/
def conjSpanOneLinkLowerConstant
    (beta : ℝ) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) : ℝ :=
  allCouplingLowerConstant (beta / (2 * n))
    (combEndpointDegree (m := m) hd x)
    (conjSpanCombScalarMass hd sigma rho T hT x)
    (collarFiniteEnergyFactor beta sigma.wilsonPotential
      (combEndpointCollar (m := m) hd x))
    (conjSpanCombExtractionBound hd sigma rho T hT x)
    (linkCombLocalKernelBound (m := m) beta hd x n)

theorem conjSpanOneLinkLowerConstant_pos
    {beta : ℝ} (hbeta : 0 < beta) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanOneLinkLowerConstant beta hd sigma rho T hT x := by
  apply allCouplingLowerConstant_pos
  · have hn : (0 : ℝ) < n := by exact_mod_cast sigma.dimension_pos
    positivity
  · exact conjSpanCombScalarMass_pos hd sigma rho T hT x
  · exact collarFiniteEnergyFactor_pos beta sigma.wilsonPotential _
  · exact conjSpanCombExtractionBound_pos hd sigma rho T hT x
  · exact linkCombLocalKernelBound_pos beta hd x n

/-- The positive-side Boltzmann average over the fixed endpoint collar is
strictly positive for every remote boundary configuration. -/
theorem endpointAverage_splitPositiveBoltzmannWeight_pos
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (sigma : ContinuousUnitaryRepData G n)
    (selected : Lambda.linkPositiveEdges tau k → Prop)
    [DecidablePred selected] (beta : ℝ)
    (remote : RemoteCoordinate selected → G) :
    0 < endpointAverage
      (ProductHaar.measure G (CollarCoordinate selected))
      (splitPositiveBoltzmannWeight
        (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta)
      remote := by
  letI : Measure.IsOpenPosMeasure
      (ProductHaar.measure G (CollarCoordinate selected)) := by
    unfold ProductHaar.measure
    infer_instance
  unfold endpointAverage
  apply (by fun_prop : Continuous fun u : CollarCoordinate selected → G ↦
      splitPositiveBoltzmannWeight
        (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta
        (u, remote)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _)
  · exact fun u ↦ (splitPositiveBoltzmannWeight_pos
      (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta
      (u, remote)).le
  · let u0 : CollarCoordinate selected → G := fun _ ↦ 1
    exact (splitPositiveBoltzmannWeight_pos
      (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta
      (u0, remote)).ne'

/-- The complete finite-energy/endpoint-mode/partition cancellation for the
physical selected comb.  The right side is the exact split numerator divided
by the physical Wilson partition function. -/
theorem conjSpanOneLinkLowerConstant_le_splitNumerator_div_partitionFunction
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    {beta : ℝ} (hbeta : 0 < beta) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    let selected := linkCombSelected (m := m) Lambda tau k hd x
    let data := FiniteSpecification.linkCoordinateCrossingData
      Lambda tau k hLambda hclosed sigma
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT x ≤
      Complex.re (gaugeFixedEndpointNumerator
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n))
        (data.endpointFeature selected) (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight
          (Lambda.linkWilsonDecomposition tau k hLambda sigma)
          selected beta)
        (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)) /
      FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta := by
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
  let muE := ProductHaar.measure G (CollarCoordinate selected)
  let muR := ProductHaar.measure G (RemoteCoordinate selected)
  let alpha := beta / (2 * n : ℝ)
  let F := splitPositiveBoltzmannWeight
    (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta
  let mode := uniformLinkConjSpanEndpointCrossMode Lambda tau k hLambda
    hclosed hd sigma rho T hT x hcollar hvisible
  let Aphi := conjSpanCombScalarMass hd sigma rho T hT x
  let c := collarFiniteEnergyFactor beta sigma.wilsonPotential
    (combEndpointCollar (m := m) hd x)
  let cost := conjSpanCombExtractionBound hd sigma rho T hT x
  let M := linkCombLocalKernelBound (m := m) beta hd x n
  let Gremote := endpointAverage muE F
  let Kremote := realExpFeatureKernel alpha (data.remoteFeature selected)
  let Q := realKernelQuadratic muR Kremote Gremote
  let numerator := gaugeFixedEndpointNumerator muE muR alpha
    (data.endpointFeature selected) (data.remoteFeature selected) F
    (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
  let partition := FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta
  letI : Measure.IsOpenPosMeasure muE := by
    dsimp only [muE, ProductHaar.measure]
    infer_instance
  letI : Measure.IsOpenPosMeasure muR := by
    dsimp only [muR, ProductHaar.measure]
    infer_instance
  have halpha : 0 < alpha := by
    have hn : (0 : ℝ) < n := by exact_mod_cast sigma.dimension_pos
    dsimp only [alpha]
    positivity
  have hc : 0 < c := by
    exact collarFiniteEnergyFactor_pos beta sigma.wilsonPotential _
  have hAphi : 0 < Aphi :=
    conjSpanCombScalarMass_pos hd sigma rho T hT x
  have hcost : 0 < cost :=
    conjSpanCombExtractionBound_pos hd sigma rho T hT x
  have hM : 0 < M := linkCombLocalKernelBound_pos beta hd x n
  have hF : ∀ u r, 0 < F (u, r) := by
    intro u r
    exact splitPositiveBoltzmannWeight_pos
      (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta (u, r)
  have hG : ∀ remote, 0 < Gremote remote := by
    intro remote
    exact endpointAverage_splitPositiveBoltzmannWeight_pos
      Lambda tau k hLambda sigma selected beta remote
  have hQ : 0 < Q := by
    exact realKernelQuadratic_pos muR Kremote
      (fun z ↦ realExpFeatureKernel_pos alpha (data.remoteFeature selected) z)
      Gremote hG
  have hmass : scalarEndpointMass muE
      (endpointScalarPart mode.lambda
        (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)) =
      Aphi := by
    exact uniformLinkConjSpanEndpointCrossMode_scalarMass_eq
      Lambda tau k hLambda hclosed hd sigma rho T hT x hcollar hvisible
  have hmodeCost : mode.extractionCost ≤ cost := by
    exact uniformLinkConjSpanEndpointCrossMode_extractionCost_le
      Lambda tau k hLambda hclosed hd sigma rho T hT x hcollar hvisible
  have hpair : ∀ u u' r, c * F (u', r) ≤ F (u, r) := by
    intro u u' remote
    exact (linkComb_splitPositiveBoltzmannWeight_pair_compare
      Lambda tau k hLambda hd x sigma hbeta.le u u' remote).1
  have hnumMode :
      (alpha ^ (combEndpointDegree (m := m) hd x) /
          (combEndpointDegree (m := m) hd x).factorial) *
          (c ^ 2 * Aphi ^ 2) * Q ≤
        mode.extractionCost * numerator.re := by
    have h := gaugeFixedEndpointNumerator_ge_finiteEnergyRemote
      muE muR (data.endpointFeature selected) (data.remoteFeature selected)
      (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar) mode
      halpha.le hc.le F (fun u r ↦ (hF u r).le) hpair
      (data.featureKernel_remoteFeature_im_zero selected)
    simpa only [hmass, Gremote, Kremote, Q, numerator] using h
  have hnumerator : 0 < numerator.re := by
    have hleft : 0 <
        (alpha ^ (combEndpointDegree (m := m) hd x) /
          (combEndpointDegree (m := m) hd x).factorial) *
          (c ^ 2 * Aphi ^ 2) * Q := by positivity
    have hprod : 0 < mode.extractionCost * numerator.re :=
      hleft.trans_le hnumMode
    have hmodePos : 0 < mode.extractionCost := by
      unfold EndpointConjugateMode.extractionCost
      exact mul_pos mode.lambdaNormSq_pos mode.coefficientNormSq_pos
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hmodePos.le) h.1)
  have hnum :
      (alpha ^ (combEndpointDegree (m := m) hd x) /
          (combEndpointDegree (m := m) hd x).factorial) *
          (c ^ 2 * Aphi ^ 2) * Q ≤ cost * numerator.re :=
    hnumMode.trans (mul_le_mul_of_nonneg_right hmodeCost hnumerator.le)
  have hden : partition ≤ M * Q := by
    dsimp only [partition]
    rw [partitionFunction_eq_reorderedSplitPartition
      Lambda tau k hLambda hclosed sigma selected beta]
    simpa only [muE, muR, alpha, F, M, Q, Kremote, Gremote] using
      reorderedSplitPartition_le_remoteQuadratic muE muR
      (realExpFeatureKernel alpha (data.endpointFeature selected)) Kremote F
      (fun u r ↦ (hF u r).le)
      (fun z ↦ (realExpFeatureKernel_pos alpha
        (data.remoteFeature selected) z).le)
      hM.le
      (realExpFeatureKernel_linkCombEndpointFeature_le
        Lambda tau k hLambda hclosed hd x sigma hbeta.le)
  have hpartition : 0 < partition :=
    FiniteVolume.partitionFunction_pos Lambda sigma.wilsonPotential beta
  have hcancel := allCouplingLowerConstant_le_correlation
    halpha.le hAphi.le hc.le hcost hM hQ hpartition hnum hden
  simpa only [conjSpanOneLinkLowerConstant, alpha, Aphi, c, cost, M,
    numerator, partition] using hcancel

/-- Concrete finite-volume one-link lower bound for the actual normalized
Wilson Gibbs expectation of the reflected conjugation-span observable. -/
theorem conjSpanOneLinkLowerConstant_le_gibbsExpectation
    (Lambda : FiniteSpecification d G) (hd : 3 ≤ d)
    (hLambda : Lambda.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Lambda.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0)
    (hcollar : combEndpointCollar (m := m) hd
        (step z (.forward (Geometry.armAxis hd))) ⊆
      Lambda.linkPositiveEdges (Geometry.armAxis hd) 0)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd
        (step z (.forward (Geometry.armAxis hd))),
      ∃ p : Lambda.linkCrossPlaquettes (Geometry.armAxis hd) 0,
        FiniteSpecification.linkCrossPositiveEdge (Geometry.armAxis hd) p.1 = e)
    (hdyn : (conjSpanReflectedOneLinkObservable hd sigma rho T z hz).support ⊆
      Lambda.dynamicEdges)
    {beta : ℝ} (hbeta : 0 < beta) :
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT
        (step z (.forward (Geometry.armAxis hd))) ≤
      Complex.re (∫ A,
        conjSpanReflectedOneLinkObservable hd sigma rho T z hz
          (Lambda.evaluate A)
        ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) := by
  let tau := Geometry.armAxis hd
  let y := step z (.forward tau)
  let selected := linkCombSelected (m := m) Lambda tau 0 hd y
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau 0 hLambda hclosed sigma
  let F := splitPositiveBoltzmannWeight
    (Lambda.linkWilsonDecomposition tau 0 hLambda sigma) selected beta
  let numerator := gaugeFixedEndpointNumerator
    (ProductHaar.measure G (CollarCoordinate selected))
    (ProductHaar.measure G (RemoteCoordinate selected))
    (beta / (2 * n)) (data.endpointFeature selected)
    (data.remoteFeature selected) F
    (linkConjSpanPhiFamily Lambda tau 0 hd sigma rho T y hcollar)
  let Z := FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta
  have hlower : conjSpanOneLinkLowerConstant beta hd sigma rho T hT y ≤
      numerator.re / Z := by
    simpa only [selected, data, F, numerator, Z] using
      conjSpanOneLinkLowerConstant_le_splitNumerator_div_partitionFunction
        Lambda tau 0 hLambda hclosed hbeta hd sigma rho T hT y hcollar hvisible
  have hy : y tau = 1 := by
    simp [y, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hsupport : (conjSpanPhi hd sigma rho T y).SupportedInLinkPositiveHalf
      tau 0 := by
    have h := conjSpanPhi_supportedInLinkPositiveHalf hd sigma rho T y
    simpa only [tau, hy, sub_self] using h
  have hcertificate := reflectedEndpointOneLink_isGaugeFixedLinkFamilyNormSquare
    Lambda tau hLambda rho (conjSpanPhi hd sigma rho T y) z hz
      (conjSpanPhi_gauge_covariant hd sigma rho T y) hsupport hdyn
  have hGibbs := Lambda.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
    tau 0 hLambda hclosed sigma beta
    (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)
    (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho
      (conjSpanPhi hd sigma rho T y) z hz)
    (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho
      (conjSpanPhi hd sigma rho T y) z hz) hcertificate
  have hpair := conjSpanReflectedOneLink_familyPairing_eq_numerator
    Lambda hd hLambda hclosed sigma rho T z hz hcollar beta
  have hZ : 0 < Z :=
    FiniteVolume.partitionFunction_pos Lambda sigma.wilsonPotential beta
  rw [hGibbs, hpair]
  apply hlower.trans_eq
  rw [div_eq_mul_inv]
  change numerator.re * Z⁻¹ = Complex.re ((Z : ℂ)⁻¹ * numerator)
  rw [show (Z : ℂ)⁻¹ = (Z⁻¹ : ℝ) by norm_cast]
  simp [mul_comm]

end DirectEndpointConstants

end

end YangMills.Gluelump.OneLink
