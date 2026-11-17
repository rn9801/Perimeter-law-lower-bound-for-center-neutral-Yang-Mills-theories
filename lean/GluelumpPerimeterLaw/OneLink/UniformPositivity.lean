/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.FiniteEnergy

/-!
# Cancellation of the growing remote boundary factor

The numerator lower bound and partition-function upper bound contain the
same positive remote quadratic form.  This file performs that cancellation
abstractly and records positivity of the resulting explicit all-coupling
constant.  The statement makes it impossible to hide any volume dependence:
all quantities other than `Q`, `numerator`, and `partition` are fixed inputs.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory

noncomputable section

universe uE uR

/-! ## Denominator estimate after endpoint/remote reordering -/

section PartitionUpper

variable {UE : Type uE} {UR : Type uR}
  [TopologicalSpace UE] [CompactSpace UE]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [T2Space UE] [Nonempty UE]
  [TopologicalSpace UR] [CompactSpace UR]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  [T2Space UR]

/-- The exactly split partition pairing, with the product coordinates
reordered so the remote pair is outermost.  A concrete gauge-fixing adapter
must prove that its partition function equals this expression (up to the
same explicit normalization used for the numerator). -/
def reorderedSplitPartition
    (muE : Measure UE) (muR : Measure UR)
    (KE : C(UE × UE, ℝ)) (KR : C(UR × UR, ℝ))
    (F : C(UE × UR, ℝ)) : ℝ :=
  ∫ z : (UR × UR) × (UE × UE),
    F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * KE z.2 * KR z.1
    ∂(muR.prod muR).prod (muE.prod muE)

/-- A uniform bound on the fixed endpoint kernel leaves precisely the
remote quadratic form of the endpoint-variable average. -/
theorem reorderedSplitPartition_le_remoteQuadratic
    (muE : Measure UE) (muR : Measure UR)
    [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]
    (KE : C(UE × UE, ℝ)) (KR : C(UR × UR, ℝ))
    (F : C(UE × UR, ℝ))
    (hF : ∀ u r, 0 ≤ F (u, r)) (hKR : ∀ z, 0 ≤ KR z)
    {M : ℝ} (hM : 0 ≤ M) (hKE : ∀ z, KE z ≤ M) :
    reorderedSplitPartition muE muR KE KR F ≤
      M * realKernelQuadratic muR KR (endpointAverage muE F) := by
  let upper : (UR × UR) × (UE × UE) → ℝ := fun z ↦
    M * (F (z.2.1, z.1.1) * F (z.2.2, z.1.2)) * KR z.1
  have hpartitionInt : Integrable
      (fun z : (UR × UR) × (UE × UE) ↦
        F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * KE z.2 * KR z.1)
      ((muR.prod muR).prod (muE.prod muE)) :=
    (by fun_prop : Continuous fun z : (UR × UR) × (UE × UE) ↦
      F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * KE z.2 * KR z.1)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hupperInt : Integrable upper ((muR.prod muR).prod (muE.prod muE)) :=
    (by fun_prop : Continuous upper).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    reorderedSplitPartition muE muR KE KR F ≤
        ∫ z, upper z ∂(muR.prod muR).prod (muE.prod muE) := by
      unfold reorderedSplitPartition
      apply integral_mono hpartitionInt hupperInt
      intro z
      have hFF : 0 ≤ F (z.2.1, z.1.1) * F (z.2.2, z.1.2) :=
        mul_nonneg (hF _ _) (hF _ _)
      calc
        F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * KE z.2 * KR z.1 ≤
            (F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * M) * KR z.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hKE z.2) hFF) (hKR z.1)
        _ = upper z := by ring
    _ = M * realKernelQuadratic muR KR (endpointAverage muE F) := by
      rw [integral_prod _ hupperInt]
      simp_rw [show ∀ rs : UR × UR,
          (∫ uv : UE × UE, upper (rs, uv) ∂muE.prod muE) =
            M * (endpointAverage muE F rs.1 * endpointAverage muE F rs.2) *
              KR rs by
        intro rs
        unfold upper
        rw [show (fun uv : UE × UE ↦
            M * (F ((rs, uv).2.1, (rs, uv).1.1) *
              F ((rs, uv).2.2, (rs, uv).1.2)) * KR (rs, uv).1) =
            fun uv : UE × UE ↦
              (M * KR rs) * (F (uv.1, rs.1) * F (uv.2, rs.2)) by
          funext uv
          ring]
        rw [integral_const_mul,
          integral_prod_mul (μ := muE) (ν := muE)
            (fun u ↦ F (u, rs.1)) (fun v ↦ F (v, rs.2))]
        simp only [endpointAverage_apply]
        ring]
      unfold realKernelQuadratic
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with rs
      ring

end PartitionUpper

/-! ## Numerator estimate with finite energy inserted -/

section NumeratorLower

variable {UE : Type uE} {UR : Type uR} {AE AR I : Type*} {N : ℕ}
  [TopologicalSpace UE] [CompactSpace UE] [T2Space UE] [Nonempty UE]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [TopologicalSpace UR] [CompactSpace UR] [T2Space UR] [Nonempty UR]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  [Fintype AE] [Fintype AR] [Fintype I]

/-- Milestones I and J combined: exact mode extraction followed by the
volume-independent finite-energy comparison leaves the same remote
quadratic form that appears in the denominator estimate. -/
theorem gaugeFixedEndpointNumerator_ge_finiteEnergyRemote
    (muE : Measure UE) (muR : Measure UR)
    [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (Phi : I → C(UE, ℂ)) (mode : EndpointConjugateMode featureE Phi N)
    {alpha c : ℝ} (halpha : 0 ≤ alpha) (hc : 0 ≤ c)
    (F : C(UE × UR, ℝ)) (hF : ∀ u r, 0 ≤ F (u, r))
    (hpair : ∀ u u' r, c * F (u', r) ≤ F (u, r))
    (himR : ∀ z, (featureKernel featureR z).im = 0) :
    (alpha ^ N / N.factorial) *
        (c ^ 2 * scalarEndpointMass muE
          (endpointScalarPart mode.lambda Phi) ^ 2) *
        realKernelQuadratic muR (realExpFeatureKernel alpha featureR)
          (endpointAverage muE F) ≤
      mode.extractionCost * Complex.re
        (gaugeFixedEndpointNumerator muE muR alpha
          featureE featureR F Phi) := by
  let H := contractedEndpointMassReal muE featureE Phi mode F
  let G := endpointAverage muE F
  let K := realExpFeatureKernel alpha featureR
  let Aphi := scalarEndpointMass muE (endpointScalarPart mode.lambda Phi)
  have hH : ∀ r, 0 ≤ H r := by
    intro r
    rw [show H r = weightedScalarEndpointMass muE F
        (endpointScalarPart mode.lambda Phi) r by
      exact contractedEndpointMassReal_apply muE featureE Phi mode F r]
    unfold weightedScalarEndpointMass
    exact integral_nonneg fun u ↦ mul_nonneg (sq_nonneg _) (hF u r)
  have hG : ∀ r, 0 ≤ G r := fun r ↦
    endpointAverage_nonneg muE F hF r
  have hAphi : 0 ≤ Aphi := by
    unfold Aphi scalarEndpointMass
    exact integral_nonneg fun u ↦ sq_nonneg _
  have hHG : ∀ r, c * Aphi * G r ≤ H r := by
    intro r
    change c * scalarEndpointMass muE
        (endpointScalarPart mode.lambda Phi) * endpointAverage muE F r ≤
      contractedEndpointMassReal muE featureE Phi mode F r
    rw [contractedEndpointMassReal_apply]
    exact weightedScalarEndpointMass_ge_average muE F
      (endpointScalarPart mode.lambda Phi) hc hpair r
  have hremote :
      (c ^ 2 * Aphi ^ 2) * realKernelQuadratic muR K G ≤
        realKernelQuadratic muR K H :=
    remoteQuadraticForm_endpointMass_lower muR K
      (fun z ↦ (realExpFeatureKernel_pos alpha featureR z).le)
      H G hH hG hc hAphi hHG
  have hcontract (r : UR) :
      contractedEndpointMass muE Phi mode F r = (H r : ℂ) := by
    rw [contractedEndpointMass_eq_ofReal_weightedScalarEndpointMass
      muE featureE Phi mode F r]
    congr 1
    exact (contractedEndpointMassReal_apply
      muE featureE Phi mode F r).symm
  have hreal : Complex.re (∫ z : UR × UR,
      featureSideFactor (contractedEndpointMass muE Phi mode F)
        (contractedEndpointMass muE Phi mode F) z *
      expFeatureKernel alpha featureR z ∂muR.prod muR) =
      realKernelQuadratic muR K H := by
    exact re_featureSideFactor_expFeatureKernel_eq_realKernelQuadratic
      muR featureR alpha (contractedEndpointMass muE Phi mode F) H
        hcontract himR
  have hmode := gaugeFixedEndpointNumerator_ge_endpointMode
    muE muR featureE featureR Phi mode alpha halpha F
  rw [hreal] at hmode
  calc
    (alpha ^ N / N.factorial) *
        (c ^ 2 * scalarEndpointMass muE
          (endpointScalarPart mode.lambda Phi) ^ 2) *
        realKernelQuadratic muR K G =
      (alpha ^ N / N.factorial) *
        ((c ^ 2 * Aphi ^ 2) * realKernelQuadratic muR K G) := by
          dsimp only [Aphi]
          ring
    _ ≤ (alpha ^ N / N.factorial) * realKernelQuadratic muR K H :=
      mul_le_mul_of_nonneg_left hremote (by positivity)
    _ ≤ _ := hmode

end NumeratorLower

/-- Cancel the same strictly positive remote quadratic form from a numerator
lower bound and a denominator upper bound. -/
theorem sharedRemoteFactor_cancel
    {a cost M Q numerator partition : ℝ}
    (ha : 0 ≤ a) (hcost : 0 < cost) (hM : 0 < M)
    (hQ : 0 < Q) (hpartition : 0 < partition)
    (hnumerator : a * Q ≤ cost * numerator)
    (hdenominator : partition ≤ M * Q) :
    a / (cost * M) ≤ numerator / partition := by
  apply (le_div_iff₀ hpartition).2
  have hqnonneg : 0 ≤ a / (cost * M) :=
    div_nonneg ha (mul_pos hcost hM).le
  calc
    a / (cost * M) * partition ≤
        a / (cost * M) * (M * Q) :=
      mul_le_mul_of_nonneg_left hdenominator hqnonneg
    _ = (a * Q) / cost := by field_simp
    _ ≤ numerator := (div_le_iff₀ hcost).2 (by simpa [mul_comm] using hnumerator)

/-- The fixed prefactor produced by endpoint-mode extraction, finite energy,
and the local crossing-kernel bound. -/
def allCouplingLowerConstant
    (alpha : ℝ) (N : ℕ) (Aphi finiteEnergy extractionCost localKernel : ℝ) : ℝ :=
  ((alpha ^ N / N.factorial) * (finiteEnergy ^ 2 * Aphi ^ 2)) /
    (extractionCost * localKernel)

/-- Every factor in the explicit lower constant is strictly positive at
positive coupling. -/
theorem allCouplingLowerConstant_pos
    {alpha Aphi finiteEnergy extractionCost localKernel : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hAphi : 0 < Aphi)
    (hfiniteEnergy : 0 < finiteEnergy)
    (hextractionCost : 0 < extractionCost)
    (hlocalKernel : 0 < localKernel) :
    0 < allCouplingLowerConstant alpha N Aphi finiteEnergy
      extractionCost localKernel := by
  unfold allCouplingLowerConstant
  positivity

/-- Direct cancellation corollary in the normalization used by the roadmap. -/
theorem allCouplingLowerConstant_le_correlation
    {alpha Aphi finiteEnergy extractionCost localKernel Q numerator partition : ℝ}
    {N : ℕ}
    (halpha : 0 ≤ alpha) (hAphi : 0 ≤ Aphi)
    (hfiniteEnergy : 0 ≤ finiteEnergy)
    (hextractionCost : 0 < extractionCost)
    (hlocalKernel : 0 < localKernel)
    (hQ : 0 < Q) (hpartition : 0 < partition)
    (hnumerator :
      (alpha ^ N / N.factorial) *
          (finiteEnergy ^ 2 * Aphi ^ 2) * Q ≤
        extractionCost * numerator)
    (hdenominator : partition ≤ localKernel * Q) :
    allCouplingLowerConstant alpha N Aphi finiteEnergy
        extractionCost localKernel ≤ numerator / partition := by
  apply sharedRemoteFactor_cancel
    (a := (alpha ^ N / N.factorial) * (finiteEnergy ^ 2 * Aphi ^ 2))
    (cost := extractionCost) (M := localKernel) (Q := Q)
  · positivity
  · exact hextractionCost
  · exact hlocalKernel
  · exact hQ
  · exact hpartition
  · exact hnumerator
  · exact hdenominator

end

end YangMills.Gluelump.OneLink
