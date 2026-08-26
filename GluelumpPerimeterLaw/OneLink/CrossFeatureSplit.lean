/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.BoundarySplit
import GluelumpPerimeterLaw.RepresentationTheory.FaithfulMatrixCoefficients
import YangMills.Gauge.LinkReflectionBridge

/-!
# Splitting coordinate crossing features

The concrete link-reflection decomposition reads each crossing half-holonomy
from one strict-positive side edge.  This file isolates that property and
proves that the complete doubled Wilson feature kernel splits exactly into
the crossing labels based on a fixed collar and those based on its
complement.  Repeated plaquette labels are retained, so no injectivity or
orientation convention is hidden.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Gauge.LinkReflection RepresentationTheory
open scoped BigOperators ComplexConjugate

noncomputable section

universe u

variable {G : Type u} {C P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [GaugeHaarProbability G]
  [Fintype P] [Fintype Q]

/-- A crossing decomposition is coordinate-based when every positive
half-holonomy is literally one side coordinate. -/
structure CoordinateCrossingData
    (D : WilsonActionDecomposition G n C P Q) where
  edge : Q → P
  crossHolonomy_eq (q : Q) (U : SideConfiguration G P) :
    D.crossHolonomy q U = U (edge q)

namespace CoordinateCrossingData

variable {D : WilsonActionDecomposition G n C P Q}
  (data : CoordinateCrossingData D)

/-- Doubled crossing labels whose side edge lies in the fixed collar. -/
abbrev EndpointLetter (selected : P → Prop) :=
  {q : Q // selected (data.edge q)} × Bool × Fin n × Fin n

/-- Doubled crossing labels whose side edge lies outside the fixed collar. -/
abbrev RemoteLetter (selected : P → Prop) :=
  {q : Q // ¬ selected (data.edge q)} × Bool × Fin n × Fin n

/-- A selected crossing feature written only in collar coordinates. -/
def endpointFeature (selected : P → Prop)
    (a : data.EndpointLetter selected) :
    C((CollarCoordinate selected → G), ℂ) :=
  matrixFeature D.representation
    (⟨data.edge a.1.1, a.1.2⟩, a.2.1, a.2.2.1, a.2.2.2)

/-- An unselected crossing feature written only in remote coordinates. -/
def remoteFeature (selected : P → Prop)
    (a : data.RemoteLetter selected) :
    C((RemoteCoordinate selected → G), ℂ) :=
  matrixFeature D.representation
    (⟨data.edge a.1.1, a.1.2⟩, a.2.1, a.2.2.1, a.2.2.2)

@[simp]
theorem crossFeature_eq_endpointFeature
    (selected : P → Prop) [DecidablePred selected]
    (a : data.EndpointLetter selected) (U : SideConfiguration G P) :
    D.crossFeature (a.1.1, a.2.1, a.2.2.1, a.2.2.2) U =
      data.endpointFeature selected a
        (splitSideMeasurableEquiv (G := G) selected U).1 := by
  rw [WilsonActionDecomposition.crossFeature, data.crossHolonomy_eq]
  rfl

@[simp]
theorem crossFeature_eq_remoteFeature
    (selected : P → Prop) [DecidablePred selected]
    (a : data.RemoteLetter selected) (U : SideConfiguration G P) :
    D.crossFeature (a.1.1, a.2.1, a.2.2.1, a.2.2.2) U =
      data.remoteFeature selected a
        (splitSideMeasurableEquiv (G := G) selected U).2 := by
  rw [WilsonActionDecomposition.crossFeature, data.crossHolonomy_eq]
  rfl

/-- Exact endpoint/remote split of the full doubled crossing kernel. -/
theorem crossKernel_eq_endpoint_add_remote
    (selected : P → Prop) [DecidablePred selected]
    (U V : SideConfiguration G P) :
    D.crossKernel (U, V) =
      featureKernel (data.endpointFeature selected)
          ((splitSideMeasurableEquiv (G := G) selected U).1,
            (splitSideMeasurableEquiv (G := G) selected V).1) +
        featureKernel (data.remoteFeature selected)
          ((splitSideMeasurableEquiv (G := G) selected U).2,
            (splitSideMeasurableEquiv (G := G) selected V).2) := by
  simp only [WilsonActionDecomposition.crossKernel, featureKernel_apply,
    Fintype.sum_prod_type]
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun q : Q ↦ selected (data.edge q))]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _hq
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    change conj (D.crossFeature (q.1, b, i, j) U) *
        D.crossFeature (q.1, b, i, j) V = _
    rw [data.crossFeature_eq_endpointFeature selected (q, b, i, j) U,
      data.crossFeature_eq_endpointFeature selected (q, b, i, j) V]
  · apply Finset.sum_congr rfl
    intro q _hq
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    change conj (D.crossFeature (q.1, b, i, j) U) *
        D.crossFeature (q.1, b, i, j) V = _
    rw [data.crossFeature_eq_remoteFeature selected (q, b, i, j) U,
      data.crossFeature_eq_remoteFeature selected (q, b, i, j) V]

/-- The doubled selected crossing-feature kernel is exactly real: each
orientation pair is twice the real part of one unitary character. -/
theorem featureKernel_endpointFeature_eq_character
    (selected : P → Prop) [DecidablePred selected]
    (z : (CollarCoordinate selected → G) ×
      (CollarCoordinate selected → G)) :
    featureKernel (data.endpointFeature selected) z =
      ((∑ q : {q : Q // selected (data.edge q)},
        2 * (D.representation.character
          (z.2 ⟨data.edge q.1, q.2⟩ *
            (z.1 ⟨data.edge q.1, q.2⟩)⁻¹)).re : ℝ) : ℂ) := by
  rw [featureKernel_apply, Fintype.sum_prod_type]
  push_cast
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [Fintype.sum_prod_type]
  let g := z.2 ⟨data.edge q.1, q.2⟩
  let h := z.1 ⟨data.edge q.1, q.2⟩
  calc
    (∑ b : Bool, ∑ i : Fin n, ∑ j : Fin n,
        conj (data.endpointFeature selected (q, b, i, j) z.1) *
          data.endpointFeature selected (q, b, i, j) z.2) =
      ∑ b : Bool, ∑ i : Fin n, ∑ j : Fin n,
        D.orientedMatrixCoefficient b i j g *
          conj (D.orientedMatrixCoefficient b i j h) := by
        apply Finset.sum_congr rfl
        intro b _hb
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [endpointFeature, matrixFeature,
          WilsonActionDecomposition.orientedMatrixCoefficient, g, h]
        split <;> simp only [ContinuousMap.coe_mk, starRingEnd_apply,
          star_star] <;> ring
    _ = 2 * (D.representation.character (g * h⁻¹)).re :=
      D.sum_orientedMatrixCoefficient_mul_conj g h
    _ = _ := rfl

theorem featureKernel_endpointFeature_im_zero
    (selected : P → Prop) [DecidablePred selected]
    (z : (CollarCoordinate selected → G) ×
      (CollarCoordinate selected → G)) :
    (featureKernel (data.endpointFeature selected) z).im = 0 := by
  rw [data.featureKernel_endpointFeature_eq_character]
  simp

/-- A coarse but completely uniform local-kernel bound.  It deliberately
retains repeated crossing plaquette labels; each contributes at most
`2 * n`. -/
theorem re_featureKernel_endpointFeature_le
    (selected : P → Prop) [DecidablePred selected]
    (z : (CollarCoordinate selected → G) ×
      (CollarCoordinate selected → G)) :
    (featureKernel (data.endpointFeature selected) z).re ≤
      2 * n * Fintype.card {q : Q // selected (data.edge q)} := by
  rw [data.featureKernel_endpointFeature_eq_character]
  simp only [Complex.ofReal_re]
  calc
    ∑ q : {q : Q // selected (data.edge q)},
        2 * (D.representation.character
          (z.2 ⟨data.edge q.1, q.2⟩ *
            (z.1 ⟨data.edge q.1, q.2⟩)⁻¹)).re ≤
      ∑ _q : {q : Q // selected (data.edge q)}, (2 * n : ℝ) := by
        apply Finset.sum_le_sum
        intro q _hq
        have hre := Complex.re_le_norm (D.representation.character
          (z.2 ⟨data.edge q.1, q.2⟩ *
            (z.1 ⟨data.edge q.1, q.2⟩)⁻¹))
        have hnorm := D.representation.norm_character_le
          (z.2 ⟨data.edge q.1, q.2⟩ *
            (z.1 ⟨data.edge q.1, q.2⟩)⁻¹)
        norm_num at hre ⊢
        nlinarith
    _ = 2 * n * Fintype.card {q : Q // selected (data.edge q)} := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-- The complementary remote family has the same exact reality property. -/
theorem featureKernel_remoteFeature_im_zero
    (selected : P → Prop) [DecidablePred selected]
    (z : (RemoteCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) :
    (featureKernel (data.remoteFeature selected) z).im = 0 := by
  simpa only [remoteFeature, endpointFeature] using
    (data.featureKernel_endpointFeature_im_zero
      (selected := fun p ↦ ¬selected p) z)

theorem expFeatureKernel_endpointFeature_eq_real
    (selected : P → Prop) [DecidablePred selected]
    (alpha : ℝ)
    (z : (CollarCoordinate selected → G) ×
      (CollarCoordinate selected → G)) :
    expFeatureKernel alpha (data.endpointFeature selected) z =
      (realExpFeatureKernel alpha (data.endpointFeature selected) z : ℂ) :=
  expFeatureKernel_eq_of_im_zero alpha _ z
    (data.featureKernel_endpointFeature_im_zero selected z)

theorem expFeatureKernel_remoteFeature_eq_real
    (selected : P → Prop) [DecidablePred selected]
    (alpha : ℝ)
    (z : (RemoteCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) :
    expFeatureKernel alpha (data.remoteFeature selected) z =
      (realExpFeatureKernel alpha (data.remoteFeature selected) z : ℂ) :=
  expFeatureKernel_eq_of_im_zero alpha _ z
    (data.featureKernel_remoteFeature_im_zero selected z)

/-- Explicit local exponential-kernel upper bound, with repeated selected
crossing labels counted rather than silently identified. -/
theorem realExpFeatureKernel_endpointFeature_le
    (selected : P → Prop) [DecidablePred selected]
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (z : (CollarCoordinate selected → G) ×
      (CollarCoordinate selected → G)) :
    realExpFeatureKernel alpha (data.endpointFeature selected) z ≤
      Real.exp (alpha *
        (2 * n * Fintype.card {q : Q // selected (data.edge q)})) :=
  realExpFeatureKernel_le_exp halpha _ z
    (data.re_featureKernel_endpointFeature_le selected z)

/-- A mode expressed in the doubled matrix coordinates of the collar embeds
exactly into the (possibly larger and possibly repeated) selected crossing
feature family. -/
noncomputable def endpointModeOfCollarMode
    (selected : P → Prop) [DecidablePred selected]
    {I : Type*} [Fintype I]
    (Phi : I → C((CollarCoordinate selected → G), ℂ)) {N : ℕ}
    (mode : EndpointConjugateMode
      (matrixFeature D.representation) Phi N)
    (qOf : CollarCoordinate selected →
      {q : Q // selected (data.edge q)})
    (hedge : ∀ e, data.edge (qOf e).1 = e.1) :
    EndpointConjugateMode (data.endpointFeature selected) Phi N := by
  let embed : MatrixFeatureLetter (CollarCoordinate selected) n →
      data.EndpointLetter selected := fun a ↦
    (qOf a.1, a.2.1, a.2.2.1, a.2.2.2)
  have hfeature (a : MatrixFeatureLetter (CollarCoordinate selected) n) :
      data.endpointFeature selected (embed a) =
        matrixFeature D.representation a := by
    ext U
    rcases a with ⟨e, b, i, j⟩
    simp only [embed, endpointFeature, matrixFeature]
    have he :
        (⟨data.edge (qOf e).1, (qOf e).2⟩ : CollarCoordinate selected) = e :=
      Subtype.ext (hedge e)
    rw [he]
  exact mode.mapFeature (data.endpointFeature selected) embed hfeature

end CoordinateCrossingData

/-! ## Concrete link-reflection coordinates -/

open Lattice.Cubic

/-- In the existing finite-specification link decomposition, every crossing
half-holonomy is literally the tangential edge in the first positive layer.
Plaquette closure supplies membership of that edge in the dynamic set. -/
def FiniteSpecification.linkCoordinateCrossingData
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [GaugeHaarProbability G]
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k) (hclosed : Lambda.PlaquetteClosed)
    (rho : Wilson.ContinuousUnitaryRepData G n) :
    CoordinateCrossingData
      (Lambda.linkWilsonDecomposition tau k hLambda rho) where
  edge p := by
    let e := FiniteSpecification.linkCrossPositiveEdge tau p.1
    have hp := Finset.mem_filter.mp p.2
    have hedyn : e ∈ Lambda.dynamicEdges :=
      hclosed p.1 hp.1
        (FiniteSpecification.linkCrossPositiveEdge_mem_boundary tau p.1 hp.2.2)
    have hsource : k < e.source tau := by
      rw [FiniteSpecification.linkCrossPositiveEdge_source_coord tau k p.1 hp.2.1]
      omega
    exact ⟨e, Finset.mem_filter.mpr ⟨hedyn, hsource⟩⟩
  crossHolonomy_eq p U := by
    unfold FiniteSpecification.linkWilsonDecomposition
    change Lambda.linkEvaluateSide tau k hLambda U
        (FiniteSpecification.linkCrossPositiveEdge tau p.1) = _
    rw [Lambda.linkEvaluateSide_apply_of_mem]

end

end YangMills.Gluelump.OneLink
