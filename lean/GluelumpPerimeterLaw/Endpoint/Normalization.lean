/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Covariance

/-!
# Canonical normalization of endpoint fields

A finite-coordinate local endpoint over a compact gauge group has a finite
uniform Euclidean bound.  Scaling by `1 / (1 + bound)` preserves support,
covariance, and nonzeroness while making every endpoint value have Euclidean
norm at most one.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [CompactSpace G]

/-- The continuous pointwise Euclidean norm of an endpoint, as a bounded
continuous real-valued function. -/
def endpointL2NormFunction (Phi : LocalField d G (Fin n → ℂ)) :
    BoundedContinuousFunction (Configuration d G) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A => endpointL2Norm (Phi A),
      continuous_norm.comp
        ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
          Phi.toContinuousMap.continuous)⟩

/-- Uniform Euclidean bound used to normalize an endpoint field. -/
def endpointL2Bound (Phi : LocalField d G (Fin n → ℂ)) : ℝ :=
  ‖endpointL2NormFunction Phi‖

omit [Group G] in
theorem endpointL2Bound_nonneg (Phi : LocalField d G (Fin n → ℂ)) :
    0 ≤ endpointL2Bound Phi :=
  norm_nonneg _

omit [Group G] in
/-- Every pointwise endpoint norm is bounded by `endpointL2Bound`. -/
theorem endpointL2Norm_le_bound (Phi : LocalField d G (Fin n → ℂ))
    (A : Configuration d G) :
    endpointL2Norm (Phi A) ≤ endpointL2Bound Phi := by
  have h := BoundedContinuousFunction.norm_coe_le_norm
    (endpointL2NormFunction Phi) A
  simpa [endpointL2NormFunction, endpointL2Norm,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), endpointL2Bound] using h

/-- The strictly positive real scale used for canonical normalization. -/
def endpointNormalizationScale (Phi : LocalField d G (Fin n → ℂ)) : ℝ :=
  (1 + endpointL2Bound Phi)⁻¹

omit [Group G] in
theorem endpointNormalizationScale_pos (Phi : LocalField d G (Fin n → ℂ)) :
    0 < endpointNormalizationScale Phi := by
  unfold endpointNormalizationScale
  apply inv_pos.mpr
  have hbound := endpointL2Bound_nonneg Phi
  linarith

/-- Canonically normalize a local endpoint by its uniform Euclidean bound. -/
def normalizedEndpoint (Phi : LocalField d G (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) :=
  Phi.postcomp
    ⟨fun v => (endpointNormalizationScale Phi : ℂ) • v,
      continuous_const_smul _⟩

omit [Group G] in
@[simp]
theorem normalizedEndpoint_apply (Phi : LocalField d G (Fin n → ℂ))
    (A : Configuration d G) :
    normalizedEndpoint Phi A =
      (endpointNormalizationScale Phi : ℂ) • Phi A :=
  rfl

omit [Group G] in
@[simp]
theorem normalizedEndpoint_support (Phi : LocalField d G (Fin n → ℂ)) :
    (normalizedEndpoint Phi).support = Phi.support :=
  rfl

omit [Group G] in
/-- Canonical normalization gives the roadmap's pointwise unit bound. -/
theorem normalizedEndpoint_l2Norm_le_one
    (Phi : LocalField d G (Fin n → ℂ)) (A : Configuration d G) :
    endpointL2Norm (normalizedEndpoint Phi A) ≤ 1 := by
  rw [normalizedEndpoint_apply]
  unfold endpointL2Norm
  rw [WithLp.toLp_smul, norm_smul]
  have hscale : ‖(endpointNormalizationScale Phi : ℂ)‖ =
      (1 + endpointL2Bound Phi)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (endpointNormalizationScale_pos Phi)]
    rfl
  rw [hscale]
  have hbound := endpointL2Norm_le_bound Phi A
  have hden : 0 < 1 + endpointL2Bound Phi := by
    have := endpointL2Bound_nonneg Phi
    linarith
  calc
    (1 + endpointL2Bound Phi)⁻¹ * ‖WithLp.toLp 2 (Phi A)‖ ≤
        (1 + endpointL2Bound Phi)⁻¹ * endpointL2Bound Phi := by
      exact mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hden))
    _ ≤ 1 := by
      rw [inv_mul_le_one₀ hden]
      linarith

omit [Group G] in
/-- A nonzero endpoint value remains nonzero after canonical normalization. -/
theorem normalizedEndpoint_ne_at
    (Phi : LocalField d G (Fin n → ℂ)) (A : Configuration d G)
    (hPhi : Phi A ≠ 0) : normalizedEndpoint Phi A ≠ 0 := by
  rw [normalizedEndpoint_apply]
  exact smul_ne_zero (by
    exact_mod_cast (endpointNormalizationScale_pos Phi).ne') hPhi

/-- Canonical normalization preserves endpoint covariance. -/
theorem GaugeCovariantAt.normalizedEndpoint
    (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : GaugeCovariantAt rho x Phi) :
    GaugeCovariantAt rho x (normalizedEndpoint Phi) := by
  intro g A
  rw [normalizedEndpoint_apply, normalizedEndpoint_apply, hPhi g A]
  unfold representationAction
  rw [Matrix.mulVec_smul]

end

end YangMills.Gluelump.Endpoint
