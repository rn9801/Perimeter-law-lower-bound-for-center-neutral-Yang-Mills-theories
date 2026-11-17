/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.FaithfulMatrixCoefficients
import YangMills.Gauge.LinkReflectionPositivity

/-!
# Detection by cross-plane Taylor words

Only the finite collar read by a half observable has to be visible from the
cross-plane plaquettes.  This file combines restriction of product Haar with
the faithful matrix-coefficient Stone--Weierstrass theorem to make that
relative statement precise.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Wilson
open Gauge.LinkReflection
open RepresentationTheory
open scoped BigOperators ComplexConjugate

noncomputable section

variable {G P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [MeasureTheory.Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
  [DecidableEq P] [Fintype Q]

/-- Restriction of a full finite coordinate family to a finset. -/
def restrictToFinset (S : Finset P) (U : P → G) : S → G :=
  fun e => U e.1

/-- Extend a collar configuration by the identity off the collar. -/
def extendFromFinset (S : Finset P) (V : S → G) : P → G :=
  fun e => if he : e ∈ S then V ⟨e, he⟩ else 1

theorem continuous_extendFromFinset (S : Finset P) :
    Continuous (extendFromFinset (G := G) S) := by
  apply continuous_pi
  intro e
  by_cases he : e ∈ S
  · simp only [extendFromFinset, dif_pos he]
    exact continuous_apply _
  · simpa [extendFromFinset, he] using
      (continuous_const : Continuous fun _ : S → G => (1 : G))

@[simp]
theorem extendFromFinset_restrictToFinset_apply
    (S : Finset P) (U : P → G) (e : P) (he : e ∈ S) :
    extendFromFinset (G := G) S (restrictToFinset S U) e = U e := by
  simp [extendFromFinset, restrictToFinset, he]

section ProductIntegration

variable [Fintype P]

/-- Coordinate restriction preserves finite product Haar. -/
theorem measurePreserving_restrictToFinset (S : Finset P) :
    MeasurePreserving (restrictToFinset (G := G) S)
      (ProductHaar.measure G P) (ProductHaar.measure G S) := by
  let T : Finset P := Finset.univ
  let e : T ≃ P :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have hreindex := ProductHaar.measurePreserving_reindex (G := G) e.symm
  have hrestrict := ProductHaar.measurePreserving_restrictOfFinsetSubset
    (G := G) (s := S) (t := T) (fun _ _ => Finset.mem_univ _)
  have hcomp := hrestrict.comp hreindex
  simpa [restrictToFinset, ProductHaar.reindex, ProductHaar.reindexEquiv,
    T, e, ProductHaar.restrictOfFinsetSubset] using hcomp

/-- Haar integration of a collar cylinder reduces to the exact collar. -/
theorem integral_comp_restrictToFinset (S : Finset P)
    (f : (S → G) → ℂ) (hf : Measurable f) :
    ∫ U, f (restrictToFinset S U) ∂ProductHaar.measure G P =
      ∫ V, f V ∂ProductHaar.measure G S := by
  let R := restrictToFinset (G := G) S
  have hR := measurePreserving_restrictToFinset (G := G) S
  have hfmap : AEStronglyMeasurable f
      (Measure.map R (ProductHaar.measure G P)) := by
    rw [hR.map_eq]
    exact hf.aestronglyMeasurable
  calc
    _ = ∫ V, f V ∂Measure.map R (ProductHaar.measure G P) :=
      (MeasureTheory.integral_map hR.measurable.aemeasurable hfmap).symm
    _ = _ := by rw [hR.map_eq]

end ProductIntegration

/-- Restriction of a continuous cylinder to its active collar. -/
def collarRestriction (S : Finset P) (f : C(P → G, ℂ)) : C(S → G, ℂ) :=
  f.comp ⟨extendFromFinset S, continuous_extendFromFinset S⟩

/-- A nonzero cylinder remains nonzero after coordinates outside a dependency
collar are set to the identity. -/
theorem collarRestriction_ne_zero (S : Finset P) (f : C(P → G, ℂ))
    (hdep : DependsOn f (S : Set P)) (hf : f ≠ 0) :
    collarRestriction S f ≠ 0 := by
  obtain ⟨U, hU⟩ : ∃ U, f U ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (ContinuousMap.ext h)
  intro hzero
  have hvalue : collarRestriction S f (restrictToFinset S U) = f U := by
    exact hdep fun e he => extendFromFinset_restrictToFinset_apply S U e he
  have := DFunLike.congr_fun hzero (restrictToFinset S U)
  simp only [map_zero, ContinuousMap.zero_apply] at this
  exact hU (hvalue ▸ this)

variable {C : Type*} [Fintype P] [Fintype C]

/-- A nonzero continuous cylinder is detected by one Taylor word whenever
every coordinate in its dependency collar is realized by a cross holonomy. -/
theorem exists_crossWord_integral_ne_zero_of_visible
    (D : WilsonActionDecomposition G n C P Q)
    (hfaithful : Function.Injective D.representation.ρ)
    (f : C(P → G, ℂ)) (S : Finset P)
    (hdep : DependsOn f (S : Set P)) (hf : f ≠ 0)
    (q : S → Q)
    (hvisible : ∀ U e, D.crossHolonomy (q e) U = U e.1) :
    ∃ (m : ℕ) (w : WilsonActionDecomposition.CrossWord Q n m),
      ∫ U, f U * D.crossMonomial w U
        ∂ProductHaar.measure G P ≠ 0 := by
  let fS := collarRestriction S f
  obtain ⟨m, v, hv⟩ := exists_matrixFeatureFinMonomial_integral_ne_zero
    D.representation hfaithful fS
    (collarRestriction_ne_zero S f hdep hf)
  let w : WilsonActionDecomposition.CrossWord Q n m := fun r =>
    (q (v r).1, (v r).2.1, (v r).2.2.1, (v r).2.2.2)
  refine ⟨m, w, ?_⟩
  have hpoint (U : P → G) :
      f U * D.crossMonomial w U =
        fS (restrictToFinset S U) *
          matrixFeatureFinMonomial D.representation v
            (restrictToFinset S U) := by
    have hfU : f U = fS (restrictToFinset S U) := by
      symm
      exact hdep fun e he =>
        extendFromFinset_restrictToFinset_apply S U e he
    rw [hfU]
    congr 1
    unfold WilsonActionDecomposition.crossMonomial
    unfold matrixFeatureFinMonomial
    rw [ContinuousMap.prod_apply]
    change (∏ r, D.crossFeature (w r) U) =
      ∏ r, matrixFeature D.representation (v r) (restrictToFinset S U)
    apply Finset.prod_congr rfl
    intro r _hr
    simp [w, WilsonActionDecomposition.crossFeature,
      WilsonActionDecomposition.orientedMatrixCoefficient, matrixFeature,
      restrictToFinset, hvisible]
  calc
    (∫ U, f U * D.crossMonomial w U ∂ProductHaar.measure G P) =
        ∫ U, fS (restrictToFinset S U) *
          matrixFeatureFinMonomial D.representation v (restrictToFinset S U)
          ∂ProductHaar.measure G P :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ V, fS V * matrixFeatureFinMonomial D.representation v V
          ∂ProductHaar.measure G S :=
      integral_comp_restrictToFinset S
        (fun V => fS V * matrixFeatureFinMonomial D.representation v V)
        (by fun_prop)
    _ ≠ 0 := hv

/-- At `beta = 0`, visible-cylinder detection is exactly nonvanishing of one
Taylor amplitude. -/
theorem exists_taylorAmplitude_zero_ne_of_visible
    (D : WilsonActionDecomposition G n C P Q)
    (hfaithful : Function.Injective D.representation.ρ)
    (F : WilsonActionDecomposition.PositiveObservable G C P)
    (S : Finset P)
    (hdep : DependsOn (fun U => F (1, U)) (S : Set P))
    (hf : (⟨fun U => F (1, U), F.continuous.comp
      (continuous_const.prodMk continuous_id)⟩ : C(P → G, ℂ)) ≠ 0)
    (q : S → Q)
    (hvisible : ∀ U e, D.crossHolonomy (q e) U = U e.1) :
    ∃ (m : ℕ) (w : WilsonActionDecomposition.CrossWord Q n m),
      D.taylorAmplitude 0 F w ≠ 0 := by
  let f : C(P → G, ℂ) :=
    ⟨fun U => F (1, U), F.continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  obtain ⟨m, w, hw⟩ := exists_crossWord_integral_ne_zero_of_visible
    D hfaithful f S hdep hf q hvisible
  refine ⟨m, w, ?_⟩
  simpa [WilsonActionDecomposition.taylorAmplitude, f] using hw

end

end YangMills.Gluelump.OneLink
