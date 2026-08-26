/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ModeExtraction

/-!
# Volume-independent finite-energy comparison

This file formalizes the measure-theoretic part of roadmap Milestone J.  The
lattice incidence estimate and Wilson-action comparison will supply the one
pointwise hypothesis `L⁻¹ G(r) ≤ F(u,r)`.  Everything after that comparison is
proved here without reference to a box.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory

noncomputable section

universe uE uR

variable {UE : Type uE} {UR : Type uR}
  [TopologicalSpace UE] [CompactSpace UE]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [TopologicalSpace UR] [CompactSpace UR]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]

/-- Haar-average squared mass of the selected scalar endpoint component. -/
def scalarEndpointMass (muE : Measure UE) (phi : C(UE, ℂ)) : ℝ :=
  ∫ u, ‖phi u‖ ^ 2 ∂muE

/-- A nonzero continuous endpoint coordinate has strictly positive squared
mass under any measure which assigns positive mass to nonempty open sets. -/
theorem scalarEndpointMass_pos
    (muE : Measure UE) [IsFiniteMeasure muE]
    [Measure.IsOpenPosMeasure muE]
    (phi : C(UE, ℂ)) (hphi : phi ≠ 0) :
    0 < scalarEndpointMass muE phi := by
  obtain ⟨u, hu⟩ : ∃ u, phi u ≠ 0 := by
    by_contra h
    push Not at h
    exact hphi (ContinuousMap.ext h)
  unfold scalarEndpointMass
  apply (phi.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ ↦ sq_nonneg _)
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)

/-- Endpoint mass left after integrating the local endpoint variables in a
half-box weight. -/
def weightedScalarEndpointMass (muE : Measure UE)
    (F : C(UE × UR, ℝ)) (phi : C(UE, ℂ)) (r : UR) : ℝ :=
  ∫ u, ‖phi u‖ ^ 2 * F (u, r) ∂muE

/-- A pointwise finite-energy comparison passes through the endpoint Haar
integral with the exact scalar endpoint mass. -/
theorem weightedScalarEndpointMass_lower
    (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) (phi : C(UE, ℂ))
    (G : C(UR, ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (hcompare : ∀ u r, c * G r ≤ F (u, r))
    (r : UR) :
    c * scalarEndpointMass muE phi * G r ≤
      weightedScalarEndpointMass muE F phi r := by
  rw [show c * scalarEndpointMass muE phi * G r =
      ∫ _u : UE, ‖phi _u‖ ^ 2 * (c * G r) ∂muE by
    unfold scalarEndpointMass
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    ring]
  unfold weightedScalarEndpointMass
  apply integral_mono
  · exact (by fun_prop : Continuous fun u : UE ↦
      ‖phi u‖ ^ 2 * (c * G r)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (by fun_prop : Continuous fun u : UE ↦
      ‖phi u‖ ^ 2 * F (u, r)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro u
    exact mul_le_mul_of_nonneg_left (hcompare u r) (sq_nonneg _)

/-! ## Averaging the endpoint collar -/

section EndpointAverage

variable [T2Space UE] [T2Space UR] [Nonempty UE]

/-- Average a positive half-box weight over the fixed endpoint collar. -/
def endpointAverage (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) : C(UR, ℝ) where
  toFun r := ∫ u, F (u, r) ∂muE
  continuous_toFun := by
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := muE) (s := Set.univ)
        (f := fun r : UR ↦ fun u : UE ↦ F (u, r))
        (by fun_prop) isCompact_univ

@[simp]
theorem endpointAverage_apply (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) (r : UR) :
    endpointAverage muE F r = ∫ u, F (u, r) ∂muE :=
  rfl

/-- Nonnegativity of the half-box weight passes to its endpoint average. -/
theorem endpointAverage_nonneg
    (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) (hF : ∀ u r, 0 ≤ F (u, r))
    (r : UR) : 0 ≤ endpointAverage muE F r := by
  rw [endpointAverage_apply]
  exact integral_nonneg fun u ↦ hF u r

/-- A pairwise finite-energy lower comparison becomes comparison with the
endpoint-variable average.  The constant is unchanged because `muE` is a
probability measure. -/
theorem finiteEnergy_endpointAverage_lower
    (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) {c : ℝ}
    (hpair : ∀ u u' r, c * F (u', r) ≤ F (u, r))
    (u : UE) (r : UR) :
    c * endpointAverage muE F r ≤ F (u, r) := by
  rw [endpointAverage_apply, ← integral_const_mul]
  calc
    ∫ u', c * F (u', r) ∂muE ≤ ∫ _u' : UE, F (u, r) ∂muE := by
      apply integral_mono
      · exact (by fun_prop : Continuous fun u' : UE ↦ c * F (u', r))
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · exact fun u' ↦ hpair u u' r
    _ = F (u, r) := by simp

/-- The matching upper pairwise comparison also passes to the endpoint
average with no volume-dependent loss. -/
theorem finiteEnergy_endpointAverage_upper
    (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) {L : ℝ}
    (hpair : ∀ u u' r, F (u, r) ≤ L * F (u', r))
    (u : UE) (r : UR) :
    F (u, r) ≤ L * endpointAverage muE F r := by
  rw [endpointAverage_apply, ← integral_const_mul]
  calc
    F (u, r) = ∫ _u' : UE, F (u, r) ∂muE := by simp
    _ ≤ ∫ u', L * F (u', r) ∂muE := by
      apply integral_mono
      · exact integrable_const _
      · exact (by fun_prop : Continuous fun u' : UE ↦ L * F (u', r))
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact fun u' ↦ hpair u u' r

/-- The finite-energy/endpoint-mass estimate in the exact form needed by
the remote quadratic-form comparison. -/
theorem weightedScalarEndpointMass_ge_average
    (muE : Measure UE) [IsProbabilityMeasure muE]
    (F : C(UE × UR, ℝ)) (phi : C(UE, ℂ)) {c : ℝ}
    (hc : 0 ≤ c)
    (hpair : ∀ u u' r, c * F (u', r) ≤ F (u, r))
    (r : UR) :
    c * scalarEndpointMass muE phi * endpointAverage muE F r ≤
      weightedScalarEndpointMass muE F phi r := by
  exact weightedScalarEndpointMass_lower muE F phi (endpointAverage muE F)
    hc (fun u r ↦ finiteEnergy_endpointAverage_lower muE F hpair u r) r

end EndpointAverage

/-! ## The real form of the contracted endpoint mode -/

section ContractedEndpointMass

variable {AE I : Type*} {N : ℕ} [Fintype AE] [Fintype I]
  [T2Space UE] [T2Space UR] [Nonempty UR]
  (muE : Measure UE) [IsProbabilityMeasure muE]

/-- The contracted complex endpoint mass from mode extraction is exactly the
complexification of the elementary real weighted squared mass. -/
theorem contractedEndpointMass_eq_ofReal_weightedScalarEndpointMass
    (featureE : AE → C(UE, ℂ)) (Phi : I → C(UE, ℂ))
    (mode : EndpointConjugateMode featureE Phi N)
    (F : C(UE × UR, ℝ)) (r : UR) :
    contractedEndpointMass muE Phi mode F r =
      (weightedScalarEndpointMass muE F
        (endpointScalarPart mode.lambda Phi) r : ℂ) := by
  rw [contractedEndpointMass_apply]
  unfold weightedScalarEndpointMass
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_assoc, Complex.mul_conj, Complex.sq_norm]
  push_cast
  ring

/-- Real continuous version of the contracted endpoint mass. -/
def contractedEndpointMassReal
    (featureE : AE → C(UE, ℂ)) (Phi : I → C(UE, ℂ))
    (mode : EndpointConjugateMode featureE Phi N)
    (F : C(UE × UR, ℝ)) : C(UR, ℝ) where
  toFun r := (contractedEndpointMass muE Phi mode F r).re
  continuous_toFun := Complex.continuous_re.comp
    (contractedEndpointMass muE Phi mode F).continuous

@[simp]
theorem contractedEndpointMassReal_apply
    (featureE : AE → C(UE, ℂ)) (Phi : I → C(UE, ℂ))
    (mode : EndpointConjugateMode featureE Phi N)
    (F : C(UE × UR, ℝ)) (r : UR) :
    contractedEndpointMassReal muE featureE Phi mode F r =
      weightedScalarEndpointMass muE F
        (endpointScalarPart mode.lambda Phi) r := by
  change (contractedEndpointMass muE Phi mode F r).re = _
  rw [contractedEndpointMass_eq_ofReal_weightedScalarEndpointMass
    muE featureE Phi mode F r]
  rfl

/-- The selected mode has a strictly positive, volume-independent endpoint
mass under full-support Haar measure. -/
theorem endpointModeScalarMass_pos
    [Measure.IsOpenPosMeasure muE]
    (featureE : AE → C(UE, ℂ)) (Phi : I → C(UE, ℂ))
    (mode : EndpointConjugateMode featureE Phi N) :
    0 < scalarEndpointMass muE (endpointScalarPart mode.lambda Phi) :=
  scalarEndpointMass_pos muE _ mode.scalar_ne_zero

end ContractedEndpointMass

/-- A real remote quadratic form with a pointwise nonnegative kernel. -/
def realKernelQuadratic (muR : Measure UR)
    (K : C(UR × UR, ℝ)) (f : C(UR, ℝ)) : ℝ :=
  ∫ z, f z.1 * f z.2 * K z ∂muR.prod muR

/-- A strictly positive pointwise kernel and a strictly positive continuous
boundary function have a strictly positive quadratic form under a
full-support probability measure. -/
theorem realKernelQuadratic_pos
    (muR : Measure UR) [IsProbabilityMeasure muR]
    [Measure.IsOpenPosMeasure muR] [Nonempty UR]
    (K : C(UR × UR, ℝ)) (hK : ∀ z, 0 < K z)
    (f : C(UR, ℝ)) (hf : ∀ r, 0 < f r) :
    0 < realKernelQuadratic muR K f := by
  let r₀ : UR := Classical.choice (inferInstance : Nonempty UR)
  unfold realKernelQuadratic
  apply (by fun_prop : Continuous fun z : UR × UR ↦
      f z.1 * f z.2 * K z).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _)
    (fun z ↦ mul_nonneg (mul_nonneg (hf z.1).le (hf z.2).le) (hK z).le)
  exact mul_ne_zero (mul_ne_zero (hf r₀).ne' (hf r₀).ne') (hK (r₀, r₀)).ne'

section RealExponentialKernel

variable {AR : Type*} [Fintype AR]

/-- Once a doubled feature kernel is known to be real, the real part of its
complex reflected pairing is exactly the elementary real quadratic form. -/
theorem re_featureSideFactor_expFeatureKernel_eq_realKernelQuadratic
    (muR : Measure UR) [IsFiniteMeasure muR]
    (featureR : AR → C(UR, ℂ)) (alpha : ℝ)
    (H : C(UR, ℂ)) (h : C(UR, ℝ))
    (hH : ∀ r, H r = (h r : ℂ))
    (him : ∀ z, (featureKernel featureR z).im = 0) :
    Complex.re (∫ z : UR × UR,
      featureSideFactor H H z * expFeatureKernel alpha featureR z
        ∂muR.prod muR) =
      realKernelQuadratic muR (realExpFeatureKernel alpha featureR) h := by
  have hint : Integrable (fun z : UR × UR ↦
      featureSideFactor H H z * expFeatureKernel alpha featureR z)
      (muR.prod muR) :=
    ((featureSideFactor H H).continuous.mul
      (expFeatureKernel alpha featureR).continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hstar_ofReal (x : ℝ) : (star (x : ℂ)).re = x := by
    rw [RCLike.star_def, Complex.conj_re]
    rfl
  calc
    Complex.re (∫ z : UR × UR,
        featureSideFactor H H z * expFeatureKernel alpha featureR z
          ∂muR.prod muR) =
        ∫ z : UR × UR,
          Complex.re (featureSideFactor H H z *
            expFeatureKernel alpha featureR z) ∂muR.prod muR := by
      exact (integral_re hint).symm
    _ = realKernelQuadratic muR (realExpFeatureKernel alpha featureR) h := by
      unfold realKernelQuadratic
      apply integral_congr_ae
      filter_upwards with z
      rw [featureSideFactor_apply, hH z.1, hH z.2,
        expFeatureKernel_eq_of_im_zero alpha featureR z (him z)]
      simp only [starRingEnd_apply, hstar_ofReal, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end RealExponentialKernel

/-- Pointwise domination of nonnegative boundary functions squares through a
pointwise nonnegative remote kernel. -/
theorem realKernelQuadratic_mono_of_pointwise
    (muR : Measure UR) [IsFiniteMeasure muR] (K : C(UR × UR, ℝ))
    (hK : ∀ z, 0 ≤ K z)
    (f g : C(UR, ℝ)) (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r)
    (hfg : ∀ r, f r ≤ g r) :
    realKernelQuadratic muR K f ≤ realKernelQuadratic muR K g := by
  unfold realKernelQuadratic
  apply integral_mono
  · exact (by fun_prop : Continuous fun z : UR × UR ↦
      f z.1 * f z.2 * K z).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (by fun_prop : Continuous fun z : UR × UR ↦
      g z.1 * g z.2 * K z).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro z
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hfg z.1) (hfg z.2) (hf z.2) (hg z.1)) (hK z)

/-- Combined endpoint-mass comparison in the form used after finite energy:
`H ≥ c A_phi G` implies `Q(H) ≥ c² A_phi² Q(G)`. -/
theorem remoteQuadraticForm_endpointMass_lower
    (muR : Measure UR) [IsFiniteMeasure muR] (K : C(UR × UR, ℝ))
    (hK : ∀ z, 0 ≤ K z)
    (H G : C(UR, ℝ)) (hH : ∀ r, 0 ≤ H r) (hG : ∀ r, 0 ≤ G r)
    {c Aphi : ℝ} (hc : 0 ≤ c) (hAphi : 0 ≤ Aphi)
    (hlower : ∀ r, c * Aphi * G r ≤ H r) :
    (c ^ 2 * Aphi ^ 2) * realKernelQuadratic muR K G ≤
      realKernelQuadratic muR K H := by
  let scaledG : C(UR, ℝ) := (c * Aphi) • G
  have hscale : 0 ≤ c * Aphi := mul_nonneg hc hAphi
  have hscaled_nonneg : ∀ r, 0 ≤ scaledG r := fun r ↦ by
    simp only [scaledG, ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hscale (hG r)
  have hscaled_le : ∀ r, scaledG r ≤ H r := fun r ↦ by
    simpa [scaledG, mul_assoc] using hlower r
  have hmono := realKernelQuadratic_mono_of_pointwise muR K hK
    scaledG H hscaled_nonneg hH hscaled_le
  calc
    (c ^ 2 * Aphi ^ 2) * realKernelQuadratic muR K G =
        realKernelQuadratic muR K scaledG := by
      unfold realKernelQuadratic scaledG
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ ≤ _ := hmono

end

end YangMills.Gluelump.OneLink
