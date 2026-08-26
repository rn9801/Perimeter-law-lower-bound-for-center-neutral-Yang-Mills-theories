/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ExpKernel

/-!
# Fixed homogeneous endpoint modes

This file records the coordinate version of the homogeneous tensor mode used
by the all-coupling proof.  In a finite feature basis, a tensor functional is
exactly a coefficient family on fixed-length feature words.  Keeping that
coordinate family explicit avoids any choice of completed tensor product and
matches the Taylor words in the existing reflection-positivity layer.

The concrete gluelump endpoint will supply this structure by expanding its
finite comb holonomies and the doubled Wilson matrix features.  The lemmas
below prove, independently of that construction, the nonzero coefficient
norm and the precise finite-dimensional Cauchy--Schwarz estimate needed for
mode extraction.
-/

namespace YangMills.Gluelump.OneLink

open scoped BigOperators ComplexConjugate

noncomputable section

universe u v w

variable {X : Type u} {A : Type v} {I : Type w} {N : ℕ}
  [TopologicalSpace X] [Fintype A] [Fintype I]

/-- A scalar component of a finite-coordinate endpoint. -/
def endpointScalarPart (lambda : I → ℂ) (Phi : I → C(X, ℂ)) : C(X, ℂ) :=
  ∑ i, lambda i • Phi i

@[simp]
theorem endpointScalarPart_apply
    (lambda : I → ℂ) (Phi : I → C(X, ℂ)) (x : X) :
    endpointScalarPart lambda Phi x = ∑ i, lambda i * Phi i x := by
  simp [endpointScalarPart]

/-- A nonzero scalar endpoint component whose conjugate is exactly one
homogeneous feature mode of degree `N`. -/
structure EndpointConjugateMode
    (feature : A → C(X, ℂ)) (Phi : I → C(X, ℂ)) (N : ℕ) where
  /-- Linear functional selecting the scalar endpoint component. -/
  lambda : I → ℂ
  /-- Coordinates of the homogeneous tensor functional. -/
  coefficient : FeatureWord A N → ℂ
  /-- The selected endpoint component is nonzero. -/
  scalar_ne_zero : endpointScalarPart lambda Phi ≠ 0
  /-- Exact homogeneous-mode identity. -/
  conj_scalar_eq (x : X) :
    conj (endpointScalarPart lambda Phi x) =
      ∑ word, coefficient word * featureMonomial feature word x

/-- The coordinate functional selecting one component of a finite family. -/
def coordinateFunctional (i₀ : I) : I → ℂ := by
  classical
  exact fun i ↦ if i = i₀ then 1 else 0

@[simp]
theorem endpointScalarPart_coordinateFunctional
    (Phi : I → C(X, ℂ)) (i₀ : I) :
    endpointScalarPart (coordinateFunctional i₀) Phi = Phi i₀ := by
  classical
  ext x
  rw [endpointScalarPart_apply]
  simp [coordinateFunctional]

/-! ## Exact homogeneous feature algebra -/

/-- An exact degree-`N` homogeneous expansion in a fixed finite feature
family.  This deliberately records coefficients, rather than membership in a
polynomial closure, because those same coefficients determine the extraction
cost later in the proof. -/
structure HomogeneousFeatureExpansion
    (feature : A → C(X, ℂ)) (N : ℕ) (f : C(X, ℂ)) where
  coefficient : FeatureWord A N → ℂ
  expansion (x : X) :
    f x = ∑ word, coefficient word * featureMonomial feature word x

namespace HomogeneousFeatureExpansion

variable {feature : A → C(X, ℂ)} {f g : C(X, ℂ)}

/-- Concatenate two fixed-length feature words. -/
def appendWord {r s : ℕ} (u : FeatureWord A r) (v : FeatureWord A s) :
    FeatureWord A (r + s) :=
  Fin.addCases u v

@[simp]
theorem appendWord_castAdd {r s : ℕ} (u : FeatureWord A r)
    (v : FeatureWord A s) (i : Fin r) :
    appendWord u v (Fin.castAdd s i) = u i := by
  simp [appendWord]

@[simp]
theorem appendWord_natAdd {r s : ℕ} (u : FeatureWord A r)
    (v : FeatureWord A s) (j : Fin s) :
    appendWord u v (Fin.natAdd r j) = v j := by
  simp [appendWord]

/-- Feature monomials turn concatenation into multiplication. -/
theorem featureMonomial_appendWord {r s : ℕ}
    (u : FeatureWord A r) (v : FeatureWord A s) (x : X) :
    featureMonomial feature (appendWord u v) x =
      featureMonomial feature u x * featureMonomial feature v x := by
  simp only [featureMonomial_apply, appendWord]
  rw [Fin.prod_univ_add]
  simp

/-- The zero function is homogeneous in every degree. -/
def zero (feature : A → C(X, ℂ)) (N : ℕ) :
    HomogeneousFeatureExpansion feature N 0 where
  coefficient := 0
  expansion x := by simp

/-- A scalar constant is homogeneous of degree zero. -/
def constant (feature : A → C(X, ℂ)) (c : ℂ) :
    HomogeneousFeatureExpansion feature 0 (ContinuousMap.const X c) where
  coefficient := fun _ ↦ c
  expansion x := by simp [featureMonomial_apply]

/-- Transport an expansion across equality of continuous functions. -/
def congr (hf : HomogeneousFeatureExpansion feature N f) {g : C(X, ℂ)}
    (hfg : f = g) : HomogeneousFeatureExpansion feature N g := by
  subst hfg
  exact hf

/-- Exact homogeneous expansions are closed under addition at fixed degree. -/
def add (hf : HomogeneousFeatureExpansion feature N f)
    (hg : HomogeneousFeatureExpansion feature N g) :
    HomogeneousFeatureExpansion feature N (f + g) where
  coefficient := hf.coefficient + hg.coefficient
  expansion x := by
    rw [ContinuousMap.add_apply, hf.expansion x, hg.expansion x]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Finite sums preserve homogeneous degree.  This is opaque only to avoid a
Lean code-generator bug for dependent finite coefficient families; its body
is fully kernel-checked below. -/
noncomputable opaque sum {J : Type*} [Fintype J] (f : J → C(X, ℂ))
    (hf : ∀ j, HomogeneousFeatureExpansion feature N (f j)) :
    HomogeneousFeatureExpansion feature N (∑ j, f j) := by
  refine
    { coefficient := fun word ↦ ∑ j, (hf j).coefficient word
      expansion := fun x ↦ ?_ }
  rw [ContinuousMap.sum_apply]
  simp_rw [(hf _).expansion x]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- Exact homogeneous expansions are closed under complex scalar
multiplication. -/
def smul (c : ℂ) (hf : HomogeneousFeatureExpansion feature N f) :
    HomogeneousFeatureExpansion feature N (c • f) where
  coefficient := c • hf.coefficient
  expansion x := by
    rw [ContinuousMap.smul_apply, hf.expansion x]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Conjugation preserves degree when the finite feature family is closed
under conjugation by an explicit involution. -/
def star (flip : A → A) (hflip_involutive : Function.Involutive flip)
    (hfeature : ∀ a, feature (flip a) = star (feature a))
    (hf : HomogeneousFeatureExpansion feature N f) :
    HomogeneousFeatureExpansion feature N (Star.star f) := by
  classical
  let e : FeatureWord A N ≃ FeatureWord A N :=
    { toFun := fun word i ↦ flip (word i)
      invFun := fun word i ↦ flip (word i)
      left_inv := fun word ↦ by funext i; exact hflip_involutive (word i)
      right_inv := fun word ↦ by funext i; exact hflip_involutive (word i) }
  refine
    { coefficient := fun word ↦ conj (hf.coefficient (e word))
      expansion := fun x ↦ ?_ }
  rw [show Star.star f x = conj (f x) by simp, hf.expansion x]
  simp only [map_sum, map_mul]
  apply Fintype.sum_equiv e
  intro word
  change conj (hf.coefficient word) *
      conj (featureMonomial feature word x) =
    conj (hf.coefficient (e (e word))) *
      featureMonomial feature (e word) x
  rw [show e (e word) = word from e.apply_symm_apply word]
  congr 1
  simp only [featureMonomial_apply, map_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  simpa [e] using congrArg (fun g : C(X, ℂ) ↦ g x) (hfeature (word i)).symm

/-- A single feature coordinate is homogeneous of degree one. -/
def coordinate (a : A) :
    HomogeneousFeatureExpansion feature 1 (feature a) := by
  classical
  exact
    { coefficient := fun word ↦ if word = fun _ ↦ a then 1 else 0
      expansion := fun x ↦ by simp [featureMonomial_apply] }

/-- Products add homogeneous degrees.  The coefficient formula uses the
canonical equivalence between a word of length `r+s` and its two restrictions,
so no quotient polynomial representation is involved. -/
def mul {r s : ℕ} (hf : HomogeneousFeatureExpansion feature r f)
    (hg : HomogeneousFeatureExpansion feature s g) :
    HomogeneousFeatureExpansion feature (r + s) (f * g) where
  coefficient word :=
    hf.coefficient (fun i ↦ word (Fin.castAdd s i)) *
      hg.coefficient (fun j ↦ word (Fin.natAdd r j))
  expansion x := by
    classical
    rw [ContinuousMap.mul_apply, hf.expansion x, hg.expansion x,
      Finset.sum_mul_sum]
    let e : (FeatureWord A r × FeatureWord A s) ≃ FeatureWord A (r + s) :=
      { toFun := fun uv ↦ appendWord uv.1 uv.2
        invFun := fun word ↦
          (fun i ↦ word (Fin.castAdd s i),
            fun j ↦ word (Fin.natAdd r j))
        left_inv := by
          rintro ⟨u, v⟩
          ext i <;> simp
        right_inv := by
          intro word
          funext i
          refine Fin.addCases (motive := fun i ↦
              appendWord
                (fun j ↦ word (Fin.castAdd s j))
                (fun j ↦ word (Fin.natAdd r j)) i = word i)
            (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [appendWord] }
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv e
    intro uv
    rcases uv with ⟨u, v⟩
    change hf.coefficient u * featureMonomial feature u x *
        (hg.coefficient v * featureMonomial feature v x) = _
    have he : e (u, v) = appendWord u v := rfl
    rw [he, featureMonomial_appendWord]
    simp only [appendWord_castAdd, appendWord_natAdd]
    ring

/-- A product of finitely many possibly different homogeneous degrees is
homogeneous of their sum.  The order is the canonical order on `Fin m`, so
the resulting word coordinates remain completely explicit. -/
noncomputable def finProduct {m : ℕ} (degree : Fin m → ℕ)
    (f : Fin m → C(X, ℂ))
    (hf : ∀ i, HomogeneousFeatureExpansion feature (degree i) (f i)) :
    HomogeneousFeatureExpansion feature (∑ i, degree i) (∏ i, f i) := by
  induction m with
  | zero =>
      simpa using constant feature 1
  | succ m ih =>
      let degreeTail : Fin m → ℕ := Fin.tail degree
      let fTail : Fin m → C(X, ℂ) := Fin.tail f
      have hTail (i : Fin m) :
          HomogeneousFeatureExpansion feature (degreeTail i) (fTail i) :=
        hf (Fin.succ i)
      let hProdTail := ih degreeTail fTail hTail
      let hHead := hf (0 : Fin (m + 1))
      have hMul := mul hHead hProdTail
      simpa [degreeTail, fTail, Fin.sum_univ_succ, Fin.prod_univ_succ] using hMul

/-- Relabel a homogeneous expansion into a larger finite feature family.
Injectivity is not required: if labels collide, their coefficients are added
exactly. -/
noncomputable def mapFeature {B : Type*} [Fintype B]
    (featureB : B → C(X, ℂ)) (embed : A → B)
    (hfeature : ∀ a, featureB (embed a) = feature a)
    (hf : HomogeneousFeatureExpansion feature N f) :
    HomogeneousFeatureExpansion featureB N f := by
  classical
  let embedWord : FeatureWord A N → FeatureWord B N :=
    fun word i ↦ embed (word i)
  refine
    { coefficient := fun wordB ↦ ∑ wordA,
        if embedWord wordA = wordB then hf.coefficient wordA else 0
      expansion := fun x ↦ ?_ }
  rw [hf.expansion x]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro wordA _hwordA
  rw [Fintype.sum_eq_single (embedWord wordA)]
  · simp only [ite_true]
    congr 1
    rw [featureMonomial_apply, featureMonomial_apply]
    apply Finset.prod_congr rfl
    intro i _hi
    exact congrArg (fun g : C(X, ℂ) ↦ g x) (hfeature (wordA i)).symm
  · intro wordB hne
    simp [Ne.symm hne]

/-- Pull a homogeneous expansion back along a continuous map. -/
def compDomain {Y : Type*} [TopologicalSpace Y] (g : C(Y, X))
    (hf : HomogeneousFeatureExpansion feature N f) :
    HomogeneousFeatureExpansion (fun a ↦ (feature a).comp g) N (f.comp g) where
  coefficient := hf.coefficient
  expansion y := by
    rw [ContinuousMap.comp_apply, hf.expansion]
    apply Finset.sum_congr rfl
    intro word _hword
    congr 1
    simp only [featureMonomial_apply, ContinuousMap.comp_apply]

end HomogeneousFeatureExpansion

/-- Construct an endpoint mode from an exact homogeneous expansion of one
nonzero coordinate.  This is the finite-coordinate form used for the
concrete comb endpoint: no choice of inner-product structure on the endpoint
space is required. -/
def EndpointConjugateMode.ofCoordinate
    (feature : A → C(X, ℂ)) (Phi : I → C(X, ℂ)) (i₀ : I)
    (coefficient : FeatureWord A N → ℂ)
    (hPhi : Phi i₀ ≠ 0)
    (hexpansion : ∀ x,
      conj (Phi i₀ x) =
        ∑ word, coefficient word * featureMonomial feature word x) :
    EndpointConjugateMode feature Phi N where
  lambda := coordinateFunctional i₀
  coefficient := coefficient
  scalar_ne_zero := by
    simpa using hPhi
  conj_scalar_eq x := by
    simpa using hexpansion x

namespace EndpointConjugateMode

variable {feature : A → C(X, ℂ)} {Phi : I → C(X, ℂ)}
  (mode : EndpointConjugateMode feature Phi N)

/-- Pull an endpoint mode back along a continuous surjection of compact
coordinate models. -/
def compDomain {Y : Type*} [TopologicalSpace Y] (g : C(Y, X))
    (hg : Function.Surjective g) :
    EndpointConjugateMode (fun a ↦ (feature a).comp g)
      (fun i ↦ (Phi i).comp g) N where
  lambda := mode.lambda
  coefficient := mode.coefficient
  scalar_ne_zero := by
    intro hzero
    apply mode.scalar_ne_zero
    ext x
    obtain ⟨y, rfl⟩ := hg x
    have hy := DFunLike.congr_fun hzero y
    simpa [endpointScalarPart_apply] using hy
  conj_scalar_eq y := by
    simpa [endpointScalarPart_apply] using mode.conj_scalar_eq (g y)

/-- Relabel the feature family used by an endpoint mode. -/
noncomputable def mapFeature {B : Type*} [Fintype B]
    (featureB : B → C(X, ℂ)) (embed : A → B)
    (hfeature : ∀ a, featureB (embed a) = feature a) :
    EndpointConjugateMode featureB Phi N := by
  let f := endpointScalarPart mode.lambda Phi
  let hstar : HomogeneousFeatureExpansion feature N (Star.star f) :=
    { coefficient := mode.coefficient
      expansion := fun x ↦ by
        change conj (f x) = _
        exact mode.conj_scalar_eq x }
  let hlift := HomogeneousFeatureExpansion.mapFeature
    featureB embed hfeature hstar
  exact
    { lambda := mode.lambda
      coefficient := hlift.coefficient
      scalar_ne_zero := mode.scalar_ne_zero
      conj_scalar_eq := fun x ↦ by
        change Star.star f x = _
        exact hlift.expansion x }

/-- Squared Euclidean norm of the scalar-component coefficients. -/
def lambdaNormSq : ℝ := ∑ i, ‖mode.lambda i‖ ^ 2

/-- Squared Euclidean norm of the homogeneous-mode coefficients. -/
def coefficientNormSq : ℝ := ∑ word, ‖mode.coefficient word‖ ^ 2

theorem exists_lambda_ne_zero : ∃ i, mode.lambda i ≠ 0 := by
  by_contra h
  push_neg at h
  apply mode.scalar_ne_zero
  ext x
  simp [endpointScalarPart, h]

theorem exists_coefficient_ne_zero : ∃ word, mode.coefficient word ≠ 0 := by
  by_contra h
  push_neg at h
  apply mode.scalar_ne_zero
  ext x
  have hx := mode.conj_scalar_eq x
  simp only [h, zero_mul, Finset.sum_const_zero] at hx
  exact star_eq_zero.mp hx

theorem lambdaNormSq_pos : 0 < mode.lambdaNormSq := by
  obtain ⟨i, hi⟩ := mode.exists_lambda_ne_zero
  unfold lambdaNormSq
  exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
    ⟨i, Finset.mem_univ i, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem coefficientNormSq_pos : 0 < mode.coefficientNormSq := by
  obtain ⟨word, hword⟩ := mode.exists_coefficient_ne_zero
  unfold coefficientNormSq
  exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
    ⟨word, Finset.mem_univ word, sq_pos_of_pos (norm_pos_iff.mpr hword)⟩

/-- The coefficient cost appearing in endpoint-mode extraction. -/
def extractionCost : ℝ := mode.lambdaNormSq * mode.coefficientNormSq

theorem extractionCost_pos : 0 < mode.extractionCost :=
  mul_pos mode.lambdaNormSq_pos mode.coefficientNormSq_pos

/-- Finite-coordinate Cauchy--Schwarz for contraction by the endpoint mode.
This is the coordinate form of the operator-norm estimate
`||M||² ≥ ||contraction M||² / (||lambda||² ||L_A||²)`. -/
theorem normSq_contraction_le
    (M : I → FeatureWord A N → ℂ) :
    ‖∑ i, ∑ word, mode.lambda i * mode.coefficient word * M i word‖ ^ 2 ≤
      mode.extractionCost *
        ∑ i, ∑ word, ‖M i word‖ ^ 2 := by
  let J := I × FeatureWord A N
  let c : J → ℂ := fun p ↦ mode.lambda p.1 * mode.coefficient p.2
  let v : J → ℂ := fun p ↦ M p.1 p.2
  have hnorm :
      ‖∑ p : J, c p * v p‖ ≤ ∑ p : J, ‖c p‖ * ‖v p‖ := by
    calc
      _ ≤ ∑ p : J, ‖c p * v p‖ := norm_sum_le _ _
      _ = _ := by apply Finset.sum_congr rfl; intro p _hp; rw [norm_mul]
  have hsq :
      (∑ p : J, ‖c p‖ * ‖v p‖) ^ 2 ≤
        (∑ p : J, ‖c p‖ ^ 2) * ∑ p : J, ‖v p‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : J ↦ ‖c p‖)
      (fun p : J ↦ ‖v p‖)
  have hleft :
      (∑ p : J, c p * v p) =
        ∑ i, ∑ word, mode.lambda i * mode.coefficient word * M i word := by
    rw [Fintype.sum_prod_type]
  have hc : (∑ p : J, ‖c p‖ ^ 2) = mode.extractionCost := by
    rw [Fintype.sum_prod_type]
    simp only [c, norm_mul, mul_pow]
    calc
      (∑ i, ∑ word,
          ‖mode.lambda i‖ ^ 2 * ‖mode.coefficient word‖ ^ 2) =
          ∑ i, ‖mode.lambda i‖ ^ 2 *
            (∑ word, ‖mode.coefficient word‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
      _ = (∑ i, ‖mode.lambda i‖ ^ 2) *
          (∑ word, ‖mode.coefficient word‖ ^ 2) := by
        rw [Finset.sum_mul]
      _ = mode.extractionCost := by
        rfl
  have hv : (∑ p : J, ‖v p‖ ^ 2) =
      ∑ i, ∑ word, ‖M i word‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [← hleft, ← hc, ← hv]
  have hsquared : ‖∑ p : J, c p * v p‖ ^ 2 ≤
      (∑ p : J, ‖c p‖ * ‖v p‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  exact hsquared.trans hsq

section Integration

open MeasureTheory

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Contracting the degree-`N` endpoint moment by the homogeneous mode gives
exactly the positive endpoint mass `|phi|²`.  This is the algebraic identity
at the heart of Milestone I. -/
theorem contraction_integral_eq_endpointMass
    (weight remoteMonomial : C(X, ℂ)) :
    (∑ i, ∑ word,
      mode.lambda i * mode.coefficient word *
        ∫ x, weight x * Phi i x * featureMonomial feature word x *
          remoteMonomial x ∂μ) =
      ∫ x, weight x * endpointScalarPart mode.lambda Phi x *
        conj (endpointScalarPart mode.lambda Phi x) * remoteMonomial x ∂μ := by
  have hint (i : I) (word : FeatureWord A N) : Integrable
      (fun x ↦ mode.lambda i * mode.coefficient word *
        (weight x * Phi i x * featureMonomial feature word x *
          remoteMonomial x)) μ :=
    (by fun_prop : Continuous fun x ↦ mode.lambda i * mode.coefficient word *
      (weight x * Phi i x * featureMonomial feature word x *
        remoteMonomial x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [show (∑ i, ∑ word,
      mode.lambda i * mode.coefficient word *
        ∫ x, weight x * Phi i x * featureMonomial feature word x *
          remoteMonomial x ∂μ) =
      ∫ x, ∑ i, ∑ word,
        mode.lambda i * mode.coefficient word *
          (weight x * Phi i x * featureMonomial feature word x *
            remoteMonomial x) ∂μ by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro word _hword
        rw [integral_const_mul]
      · intro word _hword
        exact hint i word
    · intro i _hi
      apply integrable_finsetSum
      intro word _hword
      exact hint i word]
  apply integral_congr_ae
  filter_upwards with x
  rw [mode.conj_scalar_eq x, endpointScalarPart_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _hword
  apply Finset.sum_congr rfl
  intro i _hi
  ring

end Integration

end EndpointConjugateMode

end

end YangMills.Gluelump.OneLink
