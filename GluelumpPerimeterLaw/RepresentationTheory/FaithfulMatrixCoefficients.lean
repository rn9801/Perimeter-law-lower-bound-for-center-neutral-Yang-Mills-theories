/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Wilson.Representation
import YangMills.Gauge.ProductHaar
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Faithful matrix coefficients detect continuous cylindrical functions

This is the small Stone--Weierstrass input needed by the one-link gluelump
argument.  It avoids decomposing the endpoint into irreducibles: the matrix
coefficients of any faithful finite-dimensional unitary representation,
together with their conjugates, separate every finite product of group
variables and therefore generate a dense star subalgebra.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Set Wilson MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

variable {G I : Type*} {n : ℕ} [Group G] [TopologicalSpace G]
  [CompactSpace G] [Fintype I]

/-- A coordinate, orientation, and pair of matrix indices. -/
abbrev MatrixFeatureLetter (I : Type*) (n : ℕ) :=
  I × Bool × Fin n × Fin n

/-- A matrix coefficient of one coordinate of a finite product. -/
def matrixFeature (sigma : ContinuousUnitaryRepData G n)
    (a : MatrixFeatureLetter I n) : C(I → G, ℂ) where
  toFun U := if a.2.1 then
      star ((sigma.ρ (U a.1) : Matrix (Fin n) (Fin n) ℂ) a.2.2.1 a.2.2.2)
    else (sigma.ρ (U a.1) : Matrix (Fin n) (Fin n) ℂ) a.2.2.1 a.2.2.2
  continuous_toFun := by
    have hentry : Continuous fun U : I → G =>
        (sigma.ρ (U a.1) : Matrix (Fin n) (Fin n) ℂ) a.2.2.1 a.2.2.2 :=
      (continuous_apply a.2.2.2).comp
        ((continuous_apply a.2.2.1).comp
          (continuous_subtype_val.comp
            (sigma.continuous_ρ.comp (continuous_apply a.1))))
    split
    · exact continuous_star.comp hentry
    · exact hentry

/-- A finite product of oriented coordinate matrix coefficients. -/
def matrixFeatureMonomial (sigma : ContinuousUnitaryRepData G n)
    (w : List (MatrixFeatureLetter I n)) : C(I → G, ℂ) :=
  (w.map (matrixFeature sigma)).prod

/-- The same monomial with a fixed-length word, matching the Taylor-word
indexing used by link reflection positivity. -/
def matrixFeatureFinMonomial (sigma : ContinuousUnitaryRepData G n) {m : ℕ}
    (w : Fin m → MatrixFeatureLetter I n) : C(I → G, ℂ) :=
  ∏ r, matrixFeature sigma (w r)

@[simp]
theorem matrixFeatureFinMonomial_get
    (sigma : ContinuousUnitaryRepData G n)
    (w : List (MatrixFeatureLetter I n)) :
    matrixFeatureFinMonomial sigma w.get = matrixFeatureMonomial sigma w := by
  change (∏ r, matrixFeature sigma (w.get r)) =
    (w.map (matrixFeature sigma)).prod
  rw [← List.prod_ofFn]
  congr 1
  rw [← List.ofFn_get w]
  simp

@[simp]
theorem matrixFeatureMonomial_nil
    (sigma : ContinuousUnitaryRepData G n) :
    matrixFeatureMonomial (I := I) sigma [] = 1 := rfl

@[simp]
theorem matrixFeatureMonomial_append
    (sigma : ContinuousUnitaryRepData G n)
    (u v : List (MatrixFeatureLetter I n)) :
    matrixFeatureMonomial sigma (u ++ v) =
      matrixFeatureMonomial sigma u * matrixFeatureMonomial sigma v := by
  simp [matrixFeatureMonomial]

@[simp]
theorem matrixFeatureMonomial_singleton
    (sigma : ContinuousUnitaryRepData G n)
    (a : MatrixFeatureLetter I n) :
    matrixFeatureMonomial sigma [a] = matrixFeature sigma a := by
  simp [matrixFeatureMonomial]

/-- Reverse the orientation label of one matrix coefficient. -/
def MatrixFeatureLetter.flip (a : MatrixFeatureLetter I n) :
    MatrixFeatureLetter I n :=
  (a.1, !a.2.1, a.2.2.1, a.2.2.2)

@[simp]
theorem matrixFeature_flip
    (sigma : ContinuousUnitaryRepData G n)
    (a : MatrixFeatureLetter I n) :
    matrixFeature sigma a.flip = star (matrixFeature sigma a) := by
  ext U
  cases h : a.2.1 <;> simp [matrixFeature, MatrixFeatureLetter.flip, h]

@[simp]
theorem matrixFeatureMonomial_map_flip
    (sigma : ContinuousUnitaryRepData G n)
    (w : List (MatrixFeatureLetter I n)) :
    matrixFeatureMonomial sigma (w.map MatrixFeatureLetter.flip) =
      star (matrixFeatureMonomial sigma w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      change matrixFeature sigma a.flip *
          matrixFeatureMonomial sigma (w.map MatrixFeatureLetter.flip) =
        star (matrixFeature sigma a * matrixFeatureMonomial sigma w)
      rw [matrixFeature_flip, ih, star_mul]
      exact mul_comm _ _

/-- Linear span of finite matrix-coefficient words. -/
def matrixFeatureWordSpan (sigma : ContinuousUnitaryRepData G n) :
    Submodule ℂ C(I → G, ℂ) :=
  Submodule.span ℂ (Set.range (matrixFeatureMonomial sigma))

theorem matrixFeatureMonomial_mem_wordSpan
    (sigma : ContinuousUnitaryRepData G n)
    (w : List (MatrixFeatureLetter I n)) :
    matrixFeatureMonomial sigma w ∈ matrixFeatureWordSpan sigma :=
  Submodule.subset_span ⟨w, rfl⟩

theorem matrixFeatureWordSpan_mul_mem
    (sigma : ContinuousUnitaryRepData G n)
    {f g : C(I → G, ℂ)}
    (hf : f ∈ matrixFeatureWordSpan sigma)
    (hg : g ∈ matrixFeatureWordSpan sigma) :
    f * g ∈ matrixFeatureWordSpan sigma := by
  unfold matrixFeatureWordSpan at hf hg ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro x ⟨u, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro y ⟨v, rfl⟩
      rw [← matrixFeatureMonomial_append]
      exact Submodule.subset_span ⟨u ++ v, rfl⟩
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add] using add_mem hx hy
    · intro c x _ hx
      simpa [mul_smul_comm] using Submodule.smul_mem _ c hx
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using add_mem hx hy
  · intro c x _ hx
    simpa [smul_mul_assoc] using Submodule.smul_mem _ c hx

theorem matrixFeatureWordSpan_star_mem
    (sigma : ContinuousUnitaryRepData G n)
    {f : C(I → G, ℂ)} (hf : f ∈ matrixFeatureWordSpan sigma) :
    star f ∈ matrixFeatureWordSpan sigma := by
  unfold matrixFeatureWordSpan at hf ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro x ⟨w, rfl⟩
    rw [← matrixFeatureMonomial_map_flip]
    exact Submodule.subset_span ⟨w.map MatrixFeatureLetter.flip, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa using add_mem hx hy
  · intro c x _ hx
    simpa using Submodule.smul_mem _ (star c) hx

/-- Finite linear combinations of matrix-coefficient words form the same
star algebra used in Stone--Weierstrass. -/
def matrixFeatureWordAlgebra
    (sigma : ContinuousUnitaryRepData G n) : StarSubalgebra ℂ C(I → G, ℂ) where
  carrier := matrixFeatureWordSpan (I := I) sigma
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  mul_mem' := matrixFeatureWordSpan_mul_mem sigma
  one_mem' := by
    simpa using matrixFeatureMonomial_mem_wordSpan (I := I) sigma []
  algebraMap_mem' := fun c => by
    rw [show algebraMap ℂ C(I → G, ℂ) c =
        c • (1 : C(I → G, ℂ)) by ext; simp]
    exact Submodule.smul_mem _ c (by
      simpa using matrixFeatureMonomial_mem_wordSpan (I := I) sigma [])
  star_mem' := matrixFeatureWordSpan_star_mem sigma

/-- The star algebra generated by all coordinate matrix coefficients. -/
def faithfulMatrixCoefficientAlgebra
    (sigma : ContinuousUnitaryRepData G n) : StarSubalgebra ℂ C(I → G, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range (matrixFeature (I := I) sigma))

theorem matrixFeature_false_apply
    (sigma : ContinuousUnitaryRepData G n) (e : I) (i j : Fin n)
    (U : I → G) :
    matrixFeature sigma (e, false, i, j) U =
      (sigma.ρ (U e) : Matrix (Fin n) (Fin n) ℂ) i j := by
  simp [matrixFeature]

/-- Faithfulness makes the coordinate matrix coefficients separate points of
every finite product `I → G`. -/
theorem faithfulMatrixCoefficientAlgebra_separatesPoints
    (sigma : ContinuousUnitaryRepData G n)
    (hfaithful : Function.Injective sigma.ρ) :
    (faithfulMatrixCoefficientAlgebra (I := I) sigma).SeparatesPoints := by
  intro U V hUV
  have hcoord : ∃ e : I, U e ≠ V e := by
    by_contra h
    push_neg at h
    exact hUV (funext h)
  obtain ⟨e, he⟩ := hcoord
  have hmatrix : (sigma.ρ (U e) : Matrix (Fin n) (Fin n) ℂ) ≠
      (sigma.ρ (V e) : Matrix (Fin n) (Fin n) ℂ) := by
    intro h
    apply he
    apply hfaithful
    exact Subtype.ext h
  have hentry : ∃ i j : Fin n,
      (sigma.ρ (U e) : Matrix (Fin n) (Fin n) ℂ) i j ≠
        (sigma.ρ (V e) : Matrix (Fin n) (Fin n) ℂ) i j := by
    by_contra h
    push_neg at h
    exact hmatrix (Matrix.ext fun i j => h i j)
  obtain ⟨i, j, hij⟩ := hentry
  let f := matrixFeature sigma (e, false, i, j)
  refine ⟨(f : (I → G) → ℂ), ⟨f, ?_, rfl⟩, ?_⟩
  · unfold faithfulMatrixCoefficientAlgebra
    apply StarAlgebra.subset_adjoin ℂ
    change f ∈ Set.range (matrixFeature sigma)
    exact ⟨(e, false, i, j), rfl⟩
  · simpa [f, matrixFeature_false_apply] using hij

/-- The faithful matrix-coefficient star algebra is uniformly dense. -/
theorem faithfulMatrixCoefficientAlgebra_topologicalClosure_eq_top
    (sigma : ContinuousUnitaryRepData G n)
    (hfaithful : Function.Injective sigma.ρ) :
    (faithfulMatrixCoefficientAlgebra (I := I) sigma).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (faithfulMatrixCoefficientAlgebra_separatesPoints sigma hfaithful)

theorem faithfulMatrixCoefficientAlgebra_le_wordAlgebra
    (sigma : ContinuousUnitaryRepData G n) :
    faithfulMatrixCoefficientAlgebra (I := I) sigma ≤
      matrixFeatureWordAlgebra sigma := by
  apply StarAlgebra.adjoin_le
  rintro f ⟨a, rfl⟩
  change matrixFeature sigma a ∈
    (matrixFeatureWordAlgebra (I := I) sigma : Set C(I → G, ℂ))
  simp only [matrixFeatureWordAlgebra, SetLike.mem_coe]
  simpa using matrixFeatureMonomial_mem_wordSpan (I := I) sigma [a]

/-- The actual finite-word algebra is dense; no completion is hidden in the
Taylor-word detection statement. -/
theorem matrixFeatureWordAlgebra_topologicalClosure_eq_top
    (sigma : ContinuousUnitaryRepData G n)
    (hfaithful : Function.Injective sigma.ρ) :
    (matrixFeatureWordAlgebra (I := I) sigma).topologicalClosure = ⊤ := by
  apply ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
  exact Subalgebra.separatesPoints_monotone
    (faithfulMatrixCoefficientAlgebra_le_wordAlgebra sigma)
    (faithfulMatrixCoefficientAlgebra_separatesPoints sigma hfaithful)

section HaarDetection

variable [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Gauge.GaugeHaarProbability G]
  [MeasureTheory.Measure.IsOpenPosMeasure
    (Gauge.GaugeHaarProbability.haar G)]

local instance productHaarIsOpenPosMeasure :
    MeasureTheory.Measure.IsOpenPosMeasure (Gauge.ProductHaar.measure G I) := by
  unfold Gauge.ProductHaar.measure
  infer_instance

/-- Integration against a fixed continuous factor, as a continuous linear
functional on the uniform-norm continuous functions. -/
def weightedProductHaarIntegralCLM (f : C(I → G, ℂ)) :
    C(I → G, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun p => ∫ U, f U * p U ∂Gauge.ProductHaar.measure G I
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply, mul_add]
        rw [integral_add]
        · exact (f.continuous.mul p.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (f.continuous.mul q.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using
          (MeasureTheory.integral_smul c (fun U => f U * p U)) }
    ‖f‖ fun p => by
      calc
        ‖∫ U, f U * p U ∂Gauge.ProductHaar.measure G I‖ ≤
            ∫ U, ‖f U * p U‖ ∂Gauge.ProductHaar.measure G I :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _U, ‖f‖ * ‖p‖ ∂Gauge.ProductHaar.measure G I := by
          apply integral_mono
          · exact (f.continuous.mul p.continuous).norm.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
          · exact integrable_const _
          · intro U
            change ‖f U * p U‖ ≤ ‖f‖ * ‖p‖
            rw [norm_mul]
            exact mul_le_mul (ContinuousMap.norm_coe_le_norm f U)
              (ContinuousMap.norm_coe_le_norm p U) (norm_nonneg _) (norm_nonneg _)
        _ = ‖f‖ * ‖p‖ := by simp

@[simp]
theorem weightedProductHaarIntegralCLM_apply
    (f p : C(I → G, ℂ)) :
    weightedProductHaarIntegralCLM f p =
      ∫ U, f U * p U ∂Gauge.ProductHaar.measure G I := rfl

/-- If the integral against every finite matrix word vanished, it would
vanish on their complete linear span. -/
theorem weightedIntegral_eq_zero_of_all_matrixFeatureMonomial_eq_zero
    (sigma : ContinuousUnitaryRepData G n) (f : C(I → G, ℂ))
    (hzero : ∀ w : List (MatrixFeatureLetter I n),
      ∫ U, f U * matrixFeatureMonomial sigma w U
        ∂Gauge.ProductHaar.measure G I = 0) :
    ∀ p ∈ matrixFeatureWordAlgebra sigma,
      weightedProductHaarIntegralCLM f p = 0 := by
  intro p hp
  have hp' : p ∈ matrixFeatureWordSpan sigma := by
    simpa only [matrixFeatureWordAlgebra, SetLike.mem_coe] using hp
  unfold matrixFeatureWordSpan at hp'
  refine Submodule.span_induction
    (p := fun p _ => weightedProductHaarIntegralCLM f p = 0) ?_ ?_ ?_ ?_ hp'
  · rintro p ⟨w, rfl⟩
    exact hzero w
  · exact map_zero _
  · intro p q _ _ hp hq
    rw [map_add, hp, hq, add_zero]
  · intro c p _ hp
    rw [map_smul, hp, smul_zero]

/-- A faithful finite-dimensional action representation detects every
nonzero continuous cylindrical function by one finite matrix-coefficient
word. -/
theorem exists_matrixFeatureMonomial_integral_ne_zero
    (sigma : ContinuousUnitaryRepData G n)
    (hfaithful : Function.Injective sigma.ρ)
    (f : C(I → G, ℂ)) (hf : f ≠ 0) :
    ∃ w : List (MatrixFeatureLetter I n),
      ∫ U, f U * matrixFeatureMonomial sigma w U
        ∂Gauge.ProductHaar.measure G I ≠ 0 := by
  by_contra h
  push_neg at h
  have hvanish :=
    weightedIntegral_eq_zero_of_all_matrixFeatureMonomial_eq_zero sigma f h
  let A := matrixFeatureWordAlgebra (I := I) sigma
  let L := weightedProductHaarIntegralCLM f
  have hAle : (A : Set C(I → G, ℂ)) ⊆
      (LinearMap.ker L.toLinearMap : Set C(I → G, ℂ)) := by
    intro p hp
    exact hvanish p hp
  have hclosure : closure (A : Set C(I → G, ℂ)) ⊆
      (LinearMap.ker L.toLinearMap : Set C(I → G, ℂ)) :=
    L.isClosed_ker.closure_subset_iff.mpr hAle
  have hstar : star f ∈ LinearMap.ker L.toLinearMap := by
    apply hclosure
    rw [← A.topologicalClosure_coe]
    rw [matrixFeatureWordAlgebra_topologicalClosure_eq_top sigma hfaithful]
    exact Set.mem_univ _
  have hnormIntegral : 0 < ∫ U, ‖f U‖ ^ 2
      ∂Gauge.ProductHaar.measure G I := by
    have hpoint : ∃ U, f U ≠ 0 := by
      by_contra hU
      push_neg at hU
      exact hf (ContinuousMap.ext hU)
    obtain ⟨U, hU⟩ := hpoint
    apply (f.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun _ => sq_nonneg _)
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hU)
  have hLzero : L (star f) = 0 := hstar
  have hident : L (star f) =
      ((∫ U, ‖f U‖ ^ 2 ∂Gauge.ProductHaar.measure G I : ℝ) : ℂ) := by
    change (∫ U, f U * star (f U) ∂Gauge.ProductHaar.measure G I) =
      ((∫ U, ‖f U‖ ^ 2 ∂Gauge.ProductHaar.measure G I : ℝ) : ℂ)
    calc
      _ = ∫ U, ((‖f U‖ ^ 2 : ℝ) : ℂ)
          ∂Gauge.ProductHaar.measure G I := by
        apply integral_congr_ae
        filter_upwards with U
        rw [mul_comm]
        change conj (f U) * f U = _
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      _ = _ := integral_ofReal
  have hrealzero : ∫ U, ‖f U‖ ^ 2
      ∂Gauge.ProductHaar.measure G I = 0 := by
    rw [← Complex.ofReal_eq_zero]
    rw [← hident]
    exact hLzero
  exact hnormIntegral.ne' hrealzero

/-- Fixed-length form of `exists_matrixFeatureMonomial_integral_ne_zero`. -/
theorem exists_matrixFeatureFinMonomial_integral_ne_zero
    (sigma : ContinuousUnitaryRepData G n)
    (hfaithful : Function.Injective sigma.ρ)
    (f : C(I → G, ℂ)) (hf : f ≠ 0) :
    ∃ (m : ℕ) (w : Fin m → MatrixFeatureLetter I n),
      ∫ U, f U * matrixFeatureFinMonomial sigma w U
        ∂Gauge.ProductHaar.measure G I ≠ 0 := by
  obtain ⟨w, hw⟩ :=
    exists_matrixFeatureMonomial_integral_ne_zero sigma hfaithful f hf
  refine ⟨w.length, w.get, ?_⟩
  simpa using hw

end HaarDetection

end

end YangMills.Gluelump.RepresentationTheory
