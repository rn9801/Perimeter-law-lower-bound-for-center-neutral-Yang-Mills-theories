/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.SplitGramExpansion

/-!
# Quantitative extraction of a fixed endpoint mode

This file isolates the algebraic heart of the all-coupling argument.  The
endpoint degree is fixed, while the remote degree is summed to all orders.
A split Gram certificate records exactly the output of the endpoint/remote
Taylor--Fubini expansion.  From it, finite-dimensional Cauchy--Schwarz gives
the remote exponential quadratic form with the explicit endpoint-mode cost.

The certificate is an honest interface: its `selected_le` field is precisely
the remaining analytic/combinatorial statement that the `(N,k)` terms occur
in the full numerator with coefficient
`alpha^N/N! * alpha^k/k!`.  No positivity or conclusion is built into the
definition.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

universe uE uR vE vR w

variable {UE : Type uE} {UR : Type uR}
  {AE : Type vE} {AR : Type vR} {I : Type w} {N : ℕ}
  [TopologicalSpace UE] [TopologicalSpace UR]
  [Fintype AE] [Fintype AR] [Fintype I]
  {featureE : AE → C(UE, ℂ)} {Phi : I → C(UE, ℂ)}

/-- Squared mass of all split moments with fixed endpoint degree `N` and
remote degree `k`. -/
def splitMomentNormMass
    (M : ∀ k, I → FeatureWord AE N → FeatureWord AR k → ℂ)
    (k : ℕ) : ℝ :=
  ∑ i, ∑ wordE, ∑ wordR, ‖M k i wordE wordR‖ ^ 2

/-- The selected `(N,k)` contribution of a split Gram expansion. -/
def selectedEndpointModeTerm
    (alpha : ℝ)
    (M : ∀ k, I → FeatureWord AE N → FeatureWord AR k → ℂ)
    (k : ℕ) : ℝ :=
  (alpha ^ N / N.factorial) * (alpha ^ k / k.factorial) *
    splitMomentNormMass M k

/-- Exact split-expansion data needed by mode extraction. -/
structure EndpointRemoteGramCertificate
    (AR : Type vR) [Fintype AR]
    (mode : EndpointConjugateMode featureE Phi N)
    (alpha : ℝ) (numerator : ℂ) where
  /-- Vector moments with endpoint degree `N` and arbitrary remote degree. -/
  moment : ∀ k, I → FeatureWord AE N → FeatureWord AR k → ℂ
  /-- The selected series is genuinely summable. -/
  summable_selected : Summable (selectedEndpointModeTerm alpha moment)
  /-- Nonnegative terms outside the selected endpoint degree may be dropped. -/
  selected_le :
    (∑' k, selectedEndpointModeTerm alpha moment k) ≤ Complex.re numerator

namespace EndpointRemoteGramCertificate

variable (mode : EndpointConjugateMode featureE Phi N)
  {alpha : ℝ} {numerator : ℂ}
  (certificate : EndpointRemoteGramCertificate AR mode alpha numerator)

/-- The contraction identity identifying the selected endpoint mode with
the remote moments of a scalar endpoint-mass function. -/
def ContractsToRemoteMoments
    [CompactSpace UR] [MeasurableSpace UR] [BorelSpace UR]
    [SecondCountableTopology UR]
    (muR : Measure UR) [IsProbabilityMeasure muR]
    (featureR : AR → C(UR, ℂ)) (H : C(UR, ℂ)) : Prop :=
  ∀ k (wordR : FeatureWord AR k),
    (∑ i, ∑ wordE,
      mode.lambda i * mode.coefficient wordE *
        certificate.moment k i wordE wordR) =
      featureMoment muR featureR H wordR

section Remote

variable [CompactSpace UR] [MeasurableSpace UR] [BorelSpace UR]
  [SecondCountableTopology UR]
  (muR : Measure UR) [IsProbabilityMeasure muR]
  (featureR : AR → C(UR, ℂ)) (H : C(UR, ℂ))

/-- Cauchy--Schwarz at one fixed remote degree, summed over its finite word
family. -/
theorem remoteDegreeMass_le_extractionCost_mul
    (hcontract : ContractsToRemoteMoments mode certificate muR featureR H)
    (k : ℕ) :
    (∑ wordR : FeatureWord AR k,
      ‖featureMoment muR featureR H wordR‖ ^ 2) ≤
      mode.extractionCost * splitMomentNormMass certificate.moment k := by
  calc
    (∑ wordR : FeatureWord AR k,
        ‖featureMoment muR featureR H wordR‖ ^ 2) =
        ∑ wordR : FeatureWord AR k,
          ‖∑ i, ∑ wordE,
            mode.lambda i * mode.coefficient wordE *
              certificate.moment k i wordE wordR‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro wordR _hwordR
      rw [hcontract k wordR]
    _ ≤ ∑ wordR : FeatureWord AR k,
        mode.extractionCost *
          ∑ i, ∑ wordE,
            ‖certificate.moment k i wordE wordR‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro wordR _hwordR
      exact mode.normSq_contraction_le
        (fun i wordE ↦ certificate.moment k i wordE wordR)
    _ = mode.extractionCost * splitMomentNormMass certificate.moment k := by
      unfold splitMomentNormMass
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]

/-- Quantitative endpoint-mode extraction.  The fixed endpoint coefficient
multiplies the complete remote exponential quadratic form; hence all
volume-dependent remote degrees remain available for denominator
cancellation. -/
theorem endpointMode_remotePairing_le
    (halpha : 0 ≤ alpha)
    (hcontract : ContractsToRemoteMoments mode certificate muR featureR H) :
    (alpha ^ N / N.factorial) *
        Complex.re (∫ z : UR × UR,
          featureSideFactor H H z * expFeatureKernel alpha featureR z
            ∂muR.prod muR) ≤
      mode.extractionCost * Complex.re numerator := by
  let remoteTerm : ℕ → ℝ :=
    featureMomentNormSeriesTerm muR alpha featureR H
  let selected : ℕ → ℝ :=
    selectedEndpointModeTerm alpha certificate.moment
  have hremote : Summable remoteTerm :=
    summable_featureMomentNormSeriesTerm muR alpha featureR H
  have hleft : Summable fun k ↦ (alpha ^ N / N.factorial) * remoteTerm k :=
    hremote.mul_left _
  have hright : Summable fun k ↦ mode.extractionCost * selected k :=
    certificate.summable_selected.mul_left _
  have hterm (k : ℕ) :
      (alpha ^ N / N.factorial) * remoteTerm k ≤
        mode.extractionCost * selected k := by
    have hdegree := remoteDegreeMass_le_extractionCost_mul
      mode certificate muR featureR H hcontract k
    have hk : 0 ≤ alpha ^ k / k.factorial :=
      div_nonneg (pow_nonneg halpha k) (Nat.cast_nonneg _)
    have hN : 0 ≤ alpha ^ N / N.factorial :=
      div_nonneg (pow_nonneg halpha N) (Nat.cast_nonneg _)
    unfold remoteTerm featureMomentNormSeriesTerm
    unfold selected selectedEndpointModeTerm
    calc
      (alpha ^ N / ↑N.factorial) *
          ((alpha ^ k / ↑k.factorial) *
            ∑ wordR, ‖featureMoment muR featureR H wordR‖ ^ 2) ≤
          (alpha ^ N / ↑N.factorial) *
            ((alpha ^ k / ↑k.factorial) *
              (mode.extractionCost *
                splitMomentNormMass certificate.moment k)) := by
        gcongr
      _ = mode.extractionCost *
          ((alpha ^ N / ↑N.factorial) * (alpha ^ k / ↑k.factorial) *
            splitMomentNormMass certificate.moment k) := by ring
  have hseries :
      (∑' k, (alpha ^ N / N.factorial) * remoteTerm k) ≤
        ∑' k, mode.extractionCost * selected k :=
    hleft.tsum_le_tsum hterm hright
  rw [hremote.tsum_mul_left,
    certificate.summable_selected.tsum_mul_left] at hseries
  rw [re_expFeatureKernel_pairing_self_eq_tsum_normSeries]
  have hs :
      (alpha ^ N / N.factorial) *
          (∑' k, featureMomentNormSeriesTerm muR alpha featureR H k) ≤
        mode.extractionCost *
          (∑' k, selectedEndpointModeTerm alpha certificate.moment k) := by
    simpa [remoteTerm, selected] using hseries
  exact hs.trans (mul_le_mul_of_nonneg_left certificate.selected_le
    (le_of_lt mode.extractionCost_pos))

end Remote

end EndpointRemoteGramCertificate

/-! ## Canonical certificate from the genuine split Taylor expansion -/

section SplitCertificate

variable [CompactSpace UE] [CompactSpace UR]
  [T2Space UE] [T2Space UR] [Nonempty UR]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  (muE : Measure UE) (muR : Measure UR)
  [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]

/-- The exact endpoint/remote double Taylor expansion supplies the Gram
certificate required by mode extraction.  This theorem discharges the
`selected_le` field rather than assuming it: the selected row is embedded
into the full nonnegative `(n,k)` series by `k ↦ (N,k)`. -/
noncomputable def splitGramCertificate
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    (alpha : ℝ) (halpha : 0 ≤ alpha) (F : C(UE × UR, ℝ)) :
    EndpointRemoteGramCertificate AR mode alpha
      (gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi) := by
  let f : I → C(UE × UR, ℂ) := weightedEndpointCoordinate F Phi
  let moment : ∀ k, I → FeatureWord AE N → FeatureWord AR k → ℂ :=
    fun _k i wordE wordR ↦
      splitFeatureMoment muE muR featureE featureR (f i) wordE wordR
  let total : ℕ × ℕ → ℝ :=
    splitGramTerm muE muR alpha featureE featureR f
  let embed : ℕ → ℕ × ℕ := fun k ↦ (N, k)
  have hembed : Function.Injective embed := fun k l h ↦ by
    exact congrArg Prod.snd h
  have hrow (k : ℕ) :
      selectedEndpointModeTerm alpha moment k = total (embed k) := by
    rfl
  have htotal : Summable total :=
    summable_splitGramTerm muE muR alpha featureE featureR f
  have hselected : Summable (selectedEndpointModeTerm alpha moment) := by
    exact (htotal.comp_injective hembed).congr fun k ↦ (hrow k).symm
  refine
    { moment := moment
      summable_selected := hselected
      selected_le := ?_ }
  have hsubseries :
      (∑' k, selectedEndpointModeTerm alpha moment k) ≤ ∑' degree, total degree := by
    exact Summable.tsum_le_tsum_of_inj embed hembed
      (fun degree _hdegree ↦
        splitGramTerm_nonneg muE muR halpha featureE featureR f degree)
      (fun k ↦ (hrow k).le) hselected htotal
  calc
    (∑' k, selectedEndpointModeTerm alpha moment k) ≤
        ∑' degree, total degree := hsubseries
    _ = Complex.re (∫ z : (UE × UR) × (UE × UR),
        familyFeatureSideFactor f f z *
          expFeatureKernel alpha featureE (z.1.1, z.2.1) *
          expFeatureKernel alpha featureR (z.1.2, z.2.2)
        ∂(muE.prod muR).prod (muE.prod muR)) :=
      (re_family_splitExpKernel_pairing_eq_tsum_splitGramTerm
        muE muR alpha featureE featureR f).symm
    _ = Complex.re
        (gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi) := by
      apply congrArg Complex.re
      unfold gaugeFixedEndpointNumerator
      apply integral_congr_ae
      filter_upwards with z
      rw [expFeatureKernel_boundaryFeature_apply]
      simp only [f]
      ring

/-- The scalar endpoint mass left after contracting the fixed homogeneous
mode.  It is a continuous function of the remote boundary coordinates. -/
def contractedEndpointMass
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    (F : C(UE × UR, ℝ)) : C(UR, ℂ) where
  toFun r := ∫ u, ((F (u, r) : ℝ) : ℂ) *
    endpointScalarPart mode.lambda Phi u *
      conj (endpointScalarPart mode.lambda Phi u) ∂muE
  continuous_toFun := by
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
      (μ := muE) (s := Set.univ)
      (f := fun r : UR ↦ fun u : UE ↦ ((F (u, r) : ℝ) : ℂ) *
        endpointScalarPart mode.lambda Phi u *
          conj (endpointScalarPart mode.lambda Phi u)) (by fun_prop) isCompact_univ

@[simp]
theorem contractedEndpointMass_apply
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    (F : C(UE × UR, ℝ)) (r : UR) :
    contractedEndpointMass muE Phi mode F r =
      ∫ u, ((F (u, r) : ℝ) : ℂ) *
        endpointScalarPart mode.lambda Phi u *
          conj (endpointScalarPart mode.lambda Phi u) ∂muE :=
  rfl

/-- The canonical split certificate contracts to the complete remote moments
of `contractedEndpointMass`. -/
theorem splitGramCertificate_contracts
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    (alpha : ℝ) (halpha : 0 ≤ alpha) (F : C(UE × UR, ℝ)) :
    EndpointRemoteGramCertificate.ContractsToRemoteMoments mode
      (splitGramCertificate muE muR featureE featureR Phi mode alpha halpha F)
      muR featureR (contractedEndpointMass muE Phi mode F) := by
  intro k wordR
  let modeLift := mode.compDomain (ContinuousMap.fst : C(UE × UR, UE))
    Prod.fst_surjective
  have hcontract := modeLift.contraction_integral_eq_endpointMass
    (muE.prod muR) (complexHalfWeight F)
      ((featureMonomial featureR wordR).comp ContinuousMap.snd)
  have hleft :
      (∑ i, ∑ wordE,
        mode.lambda i * mode.coefficient wordE *
          (splitGramCertificate muE muR featureE featureR Phi mode
            alpha halpha F).moment k i wordE wordR) =
      ∑ i, ∑ wordE,
        modeLift.lambda i * modeLift.coefficient wordE *
          ∫ z : UE × UR,
            complexHalfWeight F z *
              ((Phi i).comp ContinuousMap.fst) z *
              featureMonomial
                (fun a ↦ (featureE a).comp ContinuousMap.fst) wordE z *
              ((featureMonomial featureR wordR).comp ContinuousMap.snd) z
            ∂muE.prod muR := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro wordE _hwordE
    congr 2
    unfold splitGramCertificate
    simp only
    unfold splitFeatureMoment weightedEndpointCoordinate
    apply integral_congr_ae
    filter_upwards with z
    simp only [complexHalfWeight_apply, ContinuousMap.mul_apply,
      ContinuousMap.comp_apply, featureMonomial_apply]
    rfl
  rw [hleft, hcontract]
  unfold featureMoment
  rw [show (∫ z : UE × UR,
      complexHalfWeight F z *
        endpointScalarPart modeLift.lambda
          (fun i ↦ (Phi i).comp ContinuousMap.fst) z *
        conj (endpointScalarPart modeLift.lambda
          (fun i ↦ (Phi i).comp ContinuousMap.fst) z) *
        ((featureMonomial featureR wordR).comp ContinuousMap.snd) z
      ∂muE.prod muR) =
      ∫ r, contractedEndpointMass muE Phi mode F r *
        featureMonomial featureR wordR r ∂muR by
    let integrand : UE × UR → ℂ := fun z ↦
      ((F z : ℝ) : ℂ) * endpointScalarPart mode.lambda Phi z.1 *
        conj (endpointScalarPart mode.lambda Phi z.1) *
          featureMonomial featureR wordR z.2
    have hint : Integrable integrand (muE.prod muR) :=
      (by fun_prop : Continuous integrand).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [show (∫ z : UE × UR,
        complexHalfWeight F z *
          endpointScalarPart modeLift.lambda
            (fun i ↦ (Phi i).comp ContinuousMap.fst) z *
          conj (endpointScalarPart modeLift.lambda
            (fun i ↦ (Phi i).comp ContinuousMap.fst) z) *
          ((featureMonomial featureR wordR).comp ContinuousMap.snd) z
        ∂muE.prod muR) = ∫ z, integrand z ∂muE.prod muR by
      apply integral_congr_ae
      filter_upwards with z
      simp only [modeLift, EndpointConjugateMode.compDomain,
        endpointScalarPart_apply, ContinuousMap.comp_apply,
        complexHalfWeight_apply, integrand]
      rfl]
    rw [integral_prod_symm integrand hint]
    apply integral_congr_ae
    filter_upwards with r
    rw [contractedEndpointMass_apply, ← integral_mul_const]]

/-- Quantitative Milestone I in its exact split-kernel form.  The fixed
endpoint degree is extracted while every remote degree remains in the
quadratic form on the left. -/
theorem gaugeFixedEndpointNumerator_ge_endpointMode
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    (alpha : ℝ) (halpha : 0 ≤ alpha) (F : C(UE × UR, ℝ)) :
    (alpha ^ N / N.factorial) *
        Complex.re (∫ z : UR × UR,
          featureSideFactor (contractedEndpointMass muE Phi mode F)
            (contractedEndpointMass muE Phi mode F) z *
          expFeatureKernel alpha featureR z ∂muR.prod muR) ≤
      mode.extractionCost * Complex.re
        (gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi) := by
  let certificate := splitGramCertificate muE muR featureE featureR
    Phi mode alpha halpha F
  exact EndpointRemoteGramCertificate.endpointMode_remotePairing_le
    mode certificate muR featureR (contractedEndpointMass muE Phi mode F)
    halpha (splitGramCertificate_contracts muE muR featureE featureR
      Phi mode alpha halpha F)

end SplitCertificate

end

end YangMills.Gluelump.OneLink
