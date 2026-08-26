/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.GaugeFixedFactorization

/-!
# Two-parameter Gram expansion for a split exponential kernel

The fixed endpoint degree and the volume-dependent remote degree must be
expanded independently.  This file proves the resulting double Taylor--Fubini
identity directly by normal convergence.  In particular, the coefficient of
degree `(n, k)` is `alpha^n / n! * alpha^k / k!`; no ordering-dependent
binomial factor is lost.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory
open scoped BigOperators ComplexConjugate Topology

noncomputable section

universe uE uR vE vR w

variable {UE : Type uE} {UR : Type uR}
  {AE : Type vE} {AR : Type vR} {I : Type w}
  [TopologicalSpace UE] [TopologicalSpace UR]
  [Fintype AE] [Fintype AR] [Fintype I]

/-- Endpoint rank-one kernel pulled back to pairs of split boundary points. -/
def splitEndpointKernel (featureE : AE → C(UE, ℂ)) :
    C(((UE × UR) × (UE × UR)), ℂ) :=
  (featureKernel featureE).comp
    ⟨fun z ↦ (z.1.1, z.2.1), by fun_prop⟩

/-- Remote rank-one kernel pulled back to pairs of split boundary points. -/
def splitRemoteKernel (featureR : AR → C(UR, ℂ)) :
    C(((UE × UR) × (UE × UR)), ℂ) :=
  (featureKernel featureR).comp
    ⟨fun z ↦ (z.1.2, z.2.2), by fun_prop⟩

@[simp]
theorem splitEndpointKernel_apply (featureE : AE → C(UE, ℂ))
    (z : (UE × UR) × (UE × UR)) :
    splitEndpointKernel featureE z = featureKernel featureE (z.1.1, z.2.1) :=
  rfl

@[simp]
theorem splitRemoteKernel_apply (featureR : AR → C(UR, ℂ))
    (z : (UE × UR) × (UE × UR)) :
    splitRemoteKernel featureR z = featureKernel featureR (z.1.2, z.2.2) :=
  rfl

/-- The `(n,k)` Taylor integrand for independently expanded endpoint and
remote kernels. -/
def splitTaylorIntegrand (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) (degree : ℕ × ℕ) :
    C(((UE × UR) × (UE × UR)), ℂ) :=
  featureSideFactor f h *
    ((degree.1.factorial : ℂ)⁻¹ •
      (((alpha : ℂ) • splitEndpointKernel featureE) ^ degree.1)) *
    ((degree.2.factorial : ℂ)⁻¹ •
      (((alpha : ℂ) • splitRemoteKernel featureR) ^ degree.2))

variable [CompactSpace UE] [CompactSpace UR]

/-- The double Taylor family converges normally in the uniform norm. -/
theorem summable_norm_splitTaylorIntegrand (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) :
    Summable fun degree : ℕ × ℕ ↦
      ‖splitTaylorIntegrand alpha featureE featureR f h degree‖ := by
  let KE : C(((UE × UR) × (UE × UR)), ℂ) :=
    (alpha : ℂ) • splitEndpointKernel featureE
  let KR : C(((UE × UR) × (UE × UR)), ℂ) :=
    (alpha : ℂ) • splitRemoteKernel featureR
  let e : ℕ → ℝ := fun n ↦ ‖(n.factorial : ℂ)⁻¹ • KE ^ n‖
  let r : ℕ → ℝ := fun k ↦ ‖(k.factorial : ℂ)⁻¹ • KR ^ k‖
  have he : Summable e := NormedSpace.norm_expSeries_summable' KE
  have hr : Summable r := NormedSpace.norm_expSeries_summable' KR
  have her : Summable fun degree : ℕ × ℕ ↦ e degree.1 * r degree.2 := by
    rw [summable_prod_of_nonneg (fun degree ↦
      mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    constructor
    · intro n
      exact hr.mul_left (e n)
    · have hrow (n : ℕ) : (∑' k, e n * r k) = e n * ∑' k, r k :=
        hr.tsum_mul_left (e n)
      apply (he.mul_right (∑' k, r k)).congr
      intro n
      simpa [e, r] using (hrow n).symm
  have hmajor : Summable fun degree : ℕ × ℕ ↦
      ‖featureSideFactor f h‖ * (e degree.1 * r degree.2) :=
    her.mul_left _
  refine hmajor.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun degree ↦ ?_)
  unfold splitTaylorIntegrand
  change ‖featureSideFactor f h *
      ((degree.1.factorial : ℂ)⁻¹ • KE ^ degree.1) *
      ((degree.2.factorial : ℂ)⁻¹ • KR ^ degree.2)‖ ≤ _
  calc
    ‖featureSideFactor f h *
        ((degree.1.factorial : ℂ)⁻¹ • KE ^ degree.1) *
        ((degree.2.factorial : ℂ)⁻¹ • KR ^ degree.2)‖ ≤
        ‖featureSideFactor f h *
          ((degree.1.factorial : ℂ)⁻¹ • KE ^ degree.1)‖ *
          ‖(degree.2.factorial : ℂ)⁻¹ • KR ^ degree.2‖ :=
      norm_mul_le _ _
    _ ≤ (‖featureSideFactor f h‖ *
          ‖(degree.1.factorial : ℂ)⁻¹ • KE ^ degree.1‖) *
          ‖(degree.2.factorial : ℂ)⁻¹ • KR ^ degree.2‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- Pointwise summation of the double Taylor family gives the product of the
two exponential kernels. -/
theorem tsum_splitTaylorIntegrand_apply (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) (z : (UE × UR) × (UE × UR)) :
    (∑' degree : ℕ × ℕ,
      splitTaylorIntegrand alpha featureE featureR f h degree z) =
      featureSideFactor f h z *
        expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2) := by
  let e : ℕ → ℂ := fun n ↦
    (n.factorial : ℂ)⁻¹ *
      (((alpha : ℂ) * featureKernel featureE (z.1.1, z.2.1)) ^ n)
  let r : ℕ → ℂ := fun k ↦
    (k.factorial : ℂ)⁻¹ *
      (((alpha : ℂ) * featureKernel featureR (z.1.2, z.2.2)) ^ k)
  have he : Summable e := by
    apply (NormedSpace.expSeries_div_summable
      ((alpha : ℂ) * featureKernel featureE (z.1.1, z.2.1))).congr
    intro n
    simp only [e, div_eq_mul_inv]
    ring
  have hr : Summable r := by
    apply (NormedSpace.expSeries_div_summable
      ((alpha : ℂ) * featureKernel featureR (z.1.2, z.2.2))).congr
    intro k
    simp only [r, div_eq_mul_inv]
    ring
  have her : Summable fun degree : ℕ × ℕ ↦
      featureSideFactor f h z * e degree.1 * r degree.2 := by
    apply Summable.of_norm
    have hen : Summable fun n ↦ ‖e n‖ := he.norm
    have hrn : Summable fun k ↦ ‖r k‖ := hr.norm
    have hprod : Summable fun degree : ℕ × ℕ ↦
        ‖e degree.1‖ * ‖r degree.2‖ := by
      rw [summable_prod_of_nonneg (fun degree ↦
        mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      constructor
      · intro n
        exact hrn.mul_left ‖e n‖
      · simp_rw [hrn.tsum_mul_left]
        exact hen.mul_right (∑' k, ‖r k‖)
    exact (hprod.mul_left ‖featureSideFactor f h z‖).congr fun degree ↦ by
      simp only [norm_mul]
      ring
  have hintegrand (degree : ℕ × ℕ) :
      splitTaylorIntegrand alpha featureE featureR f h degree z =
        featureSideFactor f h z * e degree.1 * r degree.2 := by
    simp only [splitTaylorIntegrand, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, ContinuousMap.pow_apply,
      splitEndpointKernel_apply, splitRemoteKernel_apply, e, r, smul_eq_mul]
  simp_rw [hintegrand]
  rw [her.tsum_prod]
  have hinner (n : ℕ) :
      (∑' k, featureSideFactor f h z * e n * r k) =
        featureSideFactor f h z * e n * (∑' k, r k) := by
    rw [hr.tsum_mul_left]
  simp_rw [hinner]
  have he' : Summable fun n ↦ featureSideFactor f h z * e n :=
    he.mul_left _
  rw [he'.tsum_mul_right]
  rw [he.tsum_mul_left]
  let argE : ℂ := (alpha : ℂ) * featureKernel featureE (z.1.1, z.2.1)
  let argR : ℂ := (alpha : ℂ) * featureKernel featureR (z.1.2, z.2.2)
  have heSum : HasSum e (NormedSpace.exp argE) := by
    refine HasSum.congr_fun (NormedSpace.expSeries_div_hasSum_exp argE)
      (fun n ↦ ?_)
    change e n = argE ^ n / (n.factorial : ℂ)
    simp only [e, div_eq_mul_inv]
    ring
  have hrSum : HasSum r (NormedSpace.exp argR) := by
    refine HasSum.congr_fun (NormedSpace.expSeries_div_hasSum_exp argR)
      (fun k ↦ ?_)
    change r k = argR ^ k / (k.factorial : ℂ)
    simp only [r, div_eq_mul_inv]
    ring
  rw [heSum.tsum_eq, hrSum.tsum_eq]
  rw [expFeatureKernel_apply, expFeatureKernel_apply,
    Complex.exp_eq_exp_ℂ]

variable [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  (muE : Measure UE) (muR : Measure UR)
  [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]

/-- A moment with independently labelled endpoint and remote words. -/
def splitFeatureMoment (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (f : C(UE × UR, ℂ))
    {n k : ℕ} (wordE : FeatureWord AE n) (wordR : FeatureWord AR k) : ℂ :=
  ∫ z, f z * featureMonomial featureE wordE z.1 *
    featureMonomial featureR wordR z.2 ∂muE.prod muR

/-- Exact real `(n,k)` Gram mass of a finite endpoint-coordinate family. -/
def splitGramTerm (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (f : I → C(UE × UR, ℂ))
    (degree : ℕ × ℕ) : ℝ :=
  (alpha ^ degree.1 / degree.1.factorial) *
    (alpha ^ degree.2 / degree.2.factorial) *
      ∑ i, ∑ wordE : FeatureWord AE degree.1,
        ∑ wordR : FeatureWord AR degree.2,
          ‖splitFeatureMoment muE muR featureE featureR (f i) wordE wordR‖ ^ 2

/-- Scalar version of `splitGramTerm`. -/
def splitGramScalarTerm (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (f : C(UE × UR, ℂ))
    (degree : ℕ × ℕ) : ℝ :=
  (alpha ^ degree.1 / degree.1.factorial) *
    (alpha ^ degree.2 / degree.2.factorial) *
      ∑ wordE : FeatureWord AE degree.1,
        ∑ wordR : FeatureWord AR degree.2,
          ‖splitFeatureMoment muE muR featureE featureR f wordE wordR‖ ^ 2

/-- Fubini factorization for one endpoint word and one remote word. -/
theorem integral_splitWord_eq_moments
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) {n k : ℕ}
    (wordE : FeatureWord AE n) (wordR : FeatureWord AR k) :
    (∫ z : (UE × UR) × (UE × UR),
      featureSideFactor f h z *
        (conj (featureMonomial featureE wordE z.1.1) *
          featureMonomial featureE wordE z.2.1) *
        (conj (featureMonomial featureR wordR z.1.2) *
          featureMonomial featureR wordR z.2.2)
      ∂(muE.prod muR).prod (muE.prod muR)) =
      conj (splitFeatureMoment muE muR featureE featureR f wordE wordR) *
        splitFeatureMoment muE muR featureE featureR h wordE wordR := by
  let leftFactor : UE × UR → ℂ := fun x ↦
    conj (f x * featureMonomial featureE wordE x.1 *
      featureMonomial featureR wordR x.2)
  let rightFactor : UE × UR → ℂ := fun x ↦
    h x * featureMonomial featureE wordE x.1 *
      featureMonomial featureR wordR x.2
  have hpoint (z : (UE × UR) × (UE × UR)) :
      featureSideFactor f h z *
          (conj (featureMonomial featureE wordE z.1.1) *
            featureMonomial featureE wordE z.2.1) *
          (conj (featureMonomial featureR wordR z.1.2) *
            featureMonomial featureR wordR z.2.2) =
        leftFactor z.1 * rightFactor z.2 := by
    simp only [featureSideFactor_apply, leftFactor, rightFactor, map_mul]
    ring
  simp_rw [hpoint]
  rw [integral_prod_mul leftFactor rightFactor]
  rw [show (∫ x, leftFactor x ∂muE.prod muR) =
      conj (splitFeatureMoment muE muR featureE featureR f wordE wordR) by
    change (∫ x, conj (f x * featureMonomial featureE wordE x.1 *
      featureMonomial featureR wordR x.2) ∂muE.prod muR) = _
    rw [integral_conj]
    rfl]
  rfl

/-- One integrated double Taylor coefficient is a finite Gram sum. -/
theorem integral_splitTaylorIntegrand_eq_gram (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) (degree : ℕ × ℕ) :
    (∫ z, splitTaylorIntegrand alpha featureE featureR f h degree z
      ∂(muE.prod muR).prod (muE.prod muR)) =
      ((((alpha ^ degree.1 / degree.1.factorial : ℝ) *
        (alpha ^ degree.2 / degree.2.factorial : ℝ) : ℝ) : ℂ) *
        ∑ wordE : FeatureWord AE degree.1,
          ∑ wordR : FeatureWord AR degree.2,
            conj (splitFeatureMoment muE muR featureE featureR f wordE wordR) *
              splitFeatureMoment muE muR featureE featureR h wordE wordR) := by
  have hpoint (z : (UE × UR) × (UE × UR)) :
      splitTaylorIntegrand alpha featureE featureR f h degree z =
        ((((alpha ^ degree.1 / degree.1.factorial : ℝ) *
          (alpha ^ degree.2 / degree.2.factorial : ℝ) : ℝ) : ℂ) *
          ∑ wordE : FeatureWord AE degree.1,
            ∑ wordR : FeatureWord AR degree.2,
              featureSideFactor f h z *
                (conj (featureMonomial featureE wordE z.1.1) *
                  featureMonomial featureE wordE z.2.1) *
                (conj (featureMonomial featureR wordR z.1.2) *
                  featureMonomial featureR wordR z.2.2)) := by
    simp only [splitTaylorIntegrand, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, ContinuousMap.pow_apply,
      splitEndpointKernel_apply, splitRemoteKernel_apply]
    simp only [smul_eq_mul]
    rw [mul_pow, mul_pow,
      featureKernel_pow_eq_sum_words, featureKernel_pow_eq_sum_words]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro wordE _hwordE
    apply Finset.sum_congr rfl
    intro wordR _hwordR
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum Finset.univ]
  · apply congrArg (_ * ·)
    apply Finset.sum_congr rfl
    intro wordE _hwordE
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro wordR _hwordR
      exact integral_splitWord_eq_moments muE muR featureE featureR
        f h wordE wordR
    · intro wordR _hwordR
      exact (by fun_prop : Continuous fun z : (UE × UR) × (UE × UR) ↦
        featureSideFactor f h z *
          (conj (featureMonomial featureE wordE z.1.1) *
            featureMonomial featureE wordE z.2.1) *
          (conj (featureMonomial featureR wordR z.1.2) *
            featureMonomial featureR wordR z.2.2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro wordE _hwordE
    apply integrable_finsetSum
    intro wordR _hwordR
    exact (by fun_prop : Continuous fun z : (UE × UR) × (UE × UR) ↦
      featureSideFactor f h z *
        (conj (featureMonomial featureE wordE z.1.1) *
          featureMonomial featureE wordE z.2.1) *
        (conj (featureMonomial featureR wordR z.1.2) *
          featureMonomial featureR wordR z.2.2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Normal convergence permits termwise integration of the double series. -/
theorem tsum_integral_splitTaylorIntegrand (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) :
    (∑' degree : ℕ × ℕ,
      ∫ z, splitTaylorIntegrand alpha featureE featureR f h degree z
        ∂(muE.prod muR).prod (muE.prod muR)) =
      ∫ z, ∑' degree : ℕ × ℕ,
        splitTaylorIntegrand alpha featureE featureR f h degree z
          ∂(muE.prod muR).prod (muE.prod muR) := by
  apply integral_tsum_of_summable_integral_norm
  · intro degree
    exact (splitTaylorIntegrand alpha featureE featureR f h degree).continuous
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hnorm := summable_norm_splitTaylorIntegrand
      alpha featureE featureR f h
    refine hnorm.of_nonneg_of_le
      (fun degree ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun degree ↦ ?_)
    calc
      ∫ z, ‖splitTaylorIntegrand alpha featureE featureR f h degree z‖
          ∂(muE.prod muR).prod (muE.prod muR) ≤
          ∫ _z, ‖splitTaylorIntegrand alpha featureE featureR f h degree‖
            ∂(muE.prod muR).prod (muE.prod muR) := by
        apply integral_mono
        · exact (splitTaylorIntegrand alpha featureE featureR f h degree).continuous.norm
            |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact integrable_const _
        · intro z
          exact (splitTaylorIntegrand alpha featureE featureR f h degree).norm_coe_le_norm z
      _ = ‖splitTaylorIntegrand alpha featureE featureR f h degree‖ := by simp

/-- Exact two-parameter Taylor--Fubini expansion of the split exponential
pairing. -/
theorem splitExpKernel_pairing_eq_tsum_moments (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) :
    (∫ z : (UE × UR) × (UE × UR),
      featureSideFactor f h z *
        expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2)
      ∂(muE.prod muR).prod (muE.prod muR)) =
      ∑' degree : ℕ × ℕ,
        ((((alpha ^ degree.1 / degree.1.factorial : ℝ) *
          (alpha ^ degree.2 / degree.2.factorial : ℝ) : ℝ) : ℂ) *
          ∑ wordE : FeatureWord AE degree.1,
            ∑ wordR : FeatureWord AR degree.2,
              conj (splitFeatureMoment muE muR featureE featureR f wordE wordR) *
                splitFeatureMoment muE muR featureE featureR h wordE wordR) := by
  calc
    _ = ∫ z, ∑' degree : ℕ × ℕ,
        splitTaylorIntegrand alpha featureE featureR f h degree z
          ∂(muE.prod muR).prod (muE.prod muR) := by
      apply integral_congr_ae
      filter_upwards with z
      exact (tsum_splitTaylorIntegrand_apply
        alpha featureE featureR f h z).symm
    _ = ∑' degree : ℕ × ℕ,
        ∫ z, splitTaylorIntegrand alpha featureE featureR f h degree z
          ∂(muE.prod muR).prod (muE.prod muR) :=
      (tsum_integral_splitTaylorIntegrand muE muR
        alpha featureE featureR f h).symm
    _ = _ := by
      apply tsum_congr
      intro degree
      exact integral_splitTaylorIntegrand_eq_gram muE muR
        alpha featureE featureR f h degree

/-- On the diagonal an integrated double Taylor coefficient is exactly the
real Gram mass embedded in `ℂ`. -/
theorem integral_splitTaylorIntegrand_self_eq_ofReal (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f : C(UE × UR, ℂ)) (degree : ℕ × ℕ) :
    (∫ z, splitTaylorIntegrand alpha featureE featureR f f degree z
        ∂(muE.prod muR).prod (muE.prod muR)) =
      (splitGramScalarTerm muE muR alpha featureE featureR f degree : ℝ) := by
  rw [integral_splitTaylorIntegrand_eq_gram]
  unfold splitGramScalarTerm
  rw [show (∑ wordE : FeatureWord AE degree.1,
      ∑ wordR : FeatureWord AR degree.2,
        conj (splitFeatureMoment muE muR featureE featureR f wordE wordR) *
          splitFeatureMoment muE muR featureE featureR f wordE wordR) =
      ((∑ wordE : FeatureWord AE degree.1,
        ∑ wordR : FeatureWord AR degree.2,
          ‖splitFeatureMoment muE muR featureE featureR f wordE wordR‖ ^ 2 : ℝ) : ℂ) by
    push_cast
    apply Finset.sum_congr rfl
    intro wordE _hwordE
    apply Finset.sum_congr rfl
    intro wordR _hwordR
    rw [Complex.conj_mul']]
  push_cast
  ring

/-- Absolute summability of the integrated double Taylor coefficients. -/
theorem summable_integral_splitTaylorIntegrand (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f h : C(UE × UR, ℂ)) :
    Summable fun degree : ℕ × ℕ ↦
      ∫ z, splitTaylorIntegrand alpha featureE featureR f h degree z
        ∂(muE.prod muR).prod (muE.prod muR) := by
  apply Summable.of_norm
  have hnorm := summable_norm_splitTaylorIntegrand
    alpha featureE featureR f h
  refine hnorm.of_nonneg_of_le (fun degree ↦ norm_nonneg _) (fun degree ↦ ?_)
  calc
    ‖∫ z, splitTaylorIntegrand alpha featureE featureR f h degree z
        ∂(muE.prod muR).prod (muE.prod muR)‖ ≤
        ∫ z, ‖splitTaylorIntegrand alpha featureE featureR f h degree z‖
          ∂(muE.prod muR).prod (muE.prod muR) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _z, ‖splitTaylorIntegrand alpha featureE featureR f h degree‖
        ∂(muE.prod muR).prod (muE.prod muR) := by
      apply integral_mono
      · exact (splitTaylorIntegrand alpha featureE featureR f h degree).continuous.norm
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro z
        exact (splitTaylorIntegrand alpha featureE featureR f h degree).norm_coe_le_norm z
    _ = _ := by simp

/-- The scalar real Gram masses form a summable double series. -/
theorem summable_splitGramScalarTerm (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f : C(UE × UR, ℂ)) :
    Summable (splitGramScalarTerm muE muR alpha featureE featureR f) := by
  have hint := summable_integral_splitTaylorIntegrand muE muR
    alpha featureE featureR f f
  have hc : Summable fun degree : ℕ × ℕ ↦
      ((splitGramScalarTerm muE muR alpha featureE featureR f degree : ℝ) : ℂ) := by
    exact hint.congr fun degree ↦
      integral_splitTaylorIntegrand_self_eq_ofReal muE muR
        alpha featureE featureR f degree
  exact Complex.summable_ofReal.mp hc

/-- Summability of the finite-family double Gram series. -/
theorem summable_splitGramTerm (alpha : ℝ)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f : I → C(UE × UR, ℂ)) :
    Summable (splitGramTerm muE muR alpha featureE featureR f) := by
  classical
  have hs (i : I) := summable_splitGramScalarTerm muE muR
    alpha featureE featureR (f i)
  have hfin (s : Finset I) : Summable fun degree : ℕ × ℕ ↦
      ∑ i ∈ s, splitGramScalarTerm muE muR alpha featureE featureR
        (f i) degree := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simpa [Finset.sum_insert hi] using (hs i).add ih
  apply (hfin Finset.univ).congr
  intro degree
  change (∑ i, splitGramScalarTerm muE muR alpha featureE featureR
    (f i) degree) = splitGramTerm muE muR alpha featureE featureR f degree
  unfold splitGramTerm splitGramScalarTerm
  rw [Finset.mul_sum]

/-- At nonnegative coupling every double Gram term is nonnegative. -/
theorem splitGramTerm_nonneg {alpha : ℝ} (halpha : 0 ≤ alpha)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (f : I → C(UE × UR, ℂ)) (degree : ℕ × ℕ) :
    0 ≤ splitGramTerm muE muR alpha featureE featureR f degree := by
  unfold splitGramTerm
  positivity

/-- Exact real two-parameter Gram expansion for a finite family of endpoint
coordinates. -/
theorem re_family_splitExpKernel_pairing_eq_tsum_splitGramTerm
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (f : I → C(UE × UR, ℂ)) :
    Complex.re (∫ z : (UE × UR) × (UE × UR),
      familyFeatureSideFactor f f z *
        expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2)
      ∂(muE.prod muR).prod (muE.prod muR)) =
      ∑' degree : ℕ × ℕ,
        splitGramTerm muE muR alpha featureE featureR f degree := by
  have hscalar (i : I) :
      Complex.re (∫ z : (UE × UR) × (UE × UR),
        featureSideFactor (f i) (f i) z *
          expFeatureKernel alpha featureE (z.1.1, z.2.1) *
          expFeatureKernel alpha featureR (z.1.2, z.2.2)
        ∂(muE.prod muR).prod (muE.prod muR)) =
        ∑' degree : ℕ × ℕ,
          splitGramScalarTerm muE muR alpha featureE featureR (f i) degree := by
    rw [splitExpKernel_pairing_eq_tsum_moments]
    have hs := summable_splitGramScalarTerm muE muR
      alpha featureE featureR (f i)
    have hc : Summable fun degree : ℕ × ℕ ↦
        ((splitGramScalarTerm muE muR alpha featureE featureR
          (f i) degree : ℝ) : ℂ) := Complex.summable_ofReal.mpr hs
    have hterm (degree : ℕ × ℕ) :
        ((((alpha ^ degree.1 / degree.1.factorial : ℝ) *
          (alpha ^ degree.2 / degree.2.factorial : ℝ) : ℝ) : ℂ) *
          ∑ wordE : FeatureWord AE degree.1,
            ∑ wordR : FeatureWord AR degree.2,
              conj (splitFeatureMoment muE muR featureE featureR
                (f i) wordE wordR) *
                splitFeatureMoment muE muR featureE featureR
                  (f i) wordE wordR) =
          ((splitGramScalarTerm muE muR alpha featureE featureR
            (f i) degree : ℝ) : ℂ) := by
      rw [← integral_splitTaylorIntegrand_self_eq_ofReal muE muR]
      exact (integral_splitTaylorIntegrand_eq_gram muE muR
        alpha featureE featureR (f i) (f i) degree).symm
    have hfun : (fun degree : ℕ × ℕ ↦
        ((((alpha ^ degree.1 / degree.1.factorial : ℝ) *
          (alpha ^ degree.2 / degree.2.factorial : ℝ) : ℝ) : ℂ) *
          ∑ wordE : FeatureWord AE degree.1,
            ∑ wordR : FeatureWord AR degree.2,
              conj (splitFeatureMoment muE muR featureE featureR
                (f i) wordE wordR) *
                splitFeatureMoment muE muR featureE featureR
                  (f i) wordE wordR)) =
        fun degree ↦ ((splitGramScalarTerm muE muR alpha featureE featureR
          (f i) degree : ℝ) : ℂ) := by
      funext degree
      exact hterm degree
    rw [hfun]
    rw [Complex.re_tsum hc]
    rfl
  rw [show (∫ z : (UE × UR) × (UE × UR),
      familyFeatureSideFactor f f z *
        expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2)
      ∂(muE.prod muR).prod (muE.prod muR)) =
      ∑ i, ∫ z : (UE × UR) × (UE × UR),
        featureSideFactor (f i) (f i) z *
          expFeatureKernel alpha featureE (z.1.1, z.2.1) *
          expFeatureKernel alpha featureR (z.1.2, z.2.2)
        ∂(muE.prod muR).prod (muE.prod muR) by
    simp only [familyFeatureSideFactor, ContinuousMap.sum_apply,
      Finset.sum_mul]
    rw [integral_finsetSum]
    intro i _hi
    exact (by fun_prop : Continuous fun z : (UE × UR) × (UE × UR) ↦
      featureSideFactor (f i) (f i) z *
        expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  change Complex.reAddGroupHom _ = _
  rw [map_sum]
  change (∑ i, Complex.re (∫ z : (UE × UR) × (UE × UR),
    featureSideFactor (f i) (f i) z *
      expFeatureKernel alpha featureE (z.1.1, z.2.1) *
      expFeatureKernel alpha featureR (z.1.2, z.2.2)
    ∂(muE.prod muR).prod (muE.prod muR))) = _
  simp_rw [hscalar]
  have hs (i : I) := summable_splitGramScalarTerm muE muR
    alpha featureE featureR (f i)
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun i degree ↦
      splitGramScalarTerm muE muR alpha featureE featureR (f i) degree)
    (fun i _hi ↦ hs i)]
  apply tsum_congr
  intro degree
  unfold splitGramTerm splitGramScalarTerm
  rw [Finset.mul_sum]

end

end YangMills.Gluelump.OneLink
