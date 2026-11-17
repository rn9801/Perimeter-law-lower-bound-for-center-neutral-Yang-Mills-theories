/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.LocalField
import GluelumpPerimeterLaw.Upstream.Wilson.Representation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Endpoint covariance

This file fixes the ordinary unitary representation action used by primal
gluelump endpoint fields.  An endpoint based at `x` transforms by the Wilson
representation matrix evaluated at the gauge transformation at `x`.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open scoped Matrix

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]

/-- Standard Hermitian contraction in the fixed endpoint coordinates. -/
def hermitianPairing (v w : Fin n → ℂ) : ℂ :=
  ∑ i, star (v i) * w i

/-- Euclidean (`ℓ²`) norm on fixed endpoint coordinates. -/
def endpointL2Norm (v : Fin n → ℂ) : ℝ :=
  ‖WithLp.toLp 2 v‖

theorem hermitianPairing_eq_inner (v w : Fin n → ℂ) :
    hermitianPairing v w =
      inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) := by
  simp [hermitianPairing, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

/-- Finite-dimensional Cauchy--Schwarz for the endpoint contraction. -/
theorem norm_hermitianPairing_le (v w : Fin n → ℂ) :
    ‖hermitianPairing v w‖ ≤ endpointL2Norm v * endpointL2Norm w := by
  rw [hermitianPairing_eq_inner]
  exact norm_inner_le_norm _ _

/-- The ordinary representation action in the fixed coordinates used by
`ContinuousUnitaryRepData`. -/
def representationAction (rho : ContinuousUnitaryRepData G n) (g : G)
    (v : Fin n → ℂ) : Fin n → ℂ :=
  (rho.ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ v

@[simp]
theorem representationAction_one (rho : ContinuousUnitaryRepData G n)
    (v : Fin n → ℂ) :
    representationAction rho 1 v = v := by
  simp [representationAction]

/-- The fixed-coordinate representation formula is a left group action. -/
theorem representationAction_mul (rho : ContinuousUnitaryRepData G n)
    (g h : G) (v : Fin n → ℂ) :
    representationAction rho (g * h) v =
      representationAction rho g (representationAction rho h v) := by
  simp only [representationAction, map_mul, Matrix.UnitaryGroup.mul_val,
    Matrix.mulVec_mulVec]

/-- The representation action preserves the standard Hermitian contraction
used by screened endpoint observables. -/
theorem representationAction_pairing (rho : ContinuousUnitaryRepData G n)
    (g : G) (v w : Fin n → ℂ) :
    (∑ i, star (representationAction rho g v i) *
      representationAction rho g w i) =
      ∑ i, star (v i) * w i := by
  let U : Matrix.unitaryGroup (Fin n) ℂ := rho.ρ g
  change star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) ⬝ᵥ
      ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) = star v ⬝ᵥ w
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    show (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1
      from U.property.1]
  simp

/-- Hermitian symmetry of the fixed-coordinate endpoint pairing. -/
theorem star_hermitianPairing (v w : Fin n → ℂ) :
    star (hermitianPairing v w) = hermitianPairing w v := by
  simp [hermitianPairing, star_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Conjugating a transported endpoint pairing reverses the transport. -/
theorem star_hermitianPairing_representationAction
    (rho : ContinuousUnitaryRepData G n) (g : G) (v w : Fin n → ℂ) :
    star (hermitianPairing v (representationAction rho g w)) =
      hermitianPairing w (representationAction rho g⁻¹ v) := by
  rw [star_hermitianPairing]
  have hcancel : representationAction rho g⁻¹
      (representationAction rho g w) = w := by
    rw [← representationAction_mul]
    simp
  have hpair := representationAction_pairing rho g⁻¹
    (representationAction rho g w) v
  rw [hcancel] at hpair
  exact hpair.symm

/-- The unitary representation action preserves the endpoint Euclidean norm. -/
theorem representationAction_l2Norm (rho : ContinuousUnitaryRepData G n)
    (g : G) (v : Fin n → ℂ) :
    endpointL2Norm (representationAction rho g v) = endpointL2Norm v := by
  unfold endpointL2Norm
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
  rw [← hermitianPairing_eq_inner, ← hermitianPairing_eq_inner]
  exact congrArg Complex.re (representationAction_pairing rho g v v)

/-- Gauge covariance of a local endpoint based at `x`. -/
def GaugeCovariantAt (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ)) : Prop :=
  ∀ g : GaugeTransformation d G, ∀ A : Configuration d G,
    Phi (gaugeTransform g A) = representationAction rho (g x) (Phi A)

/-- Gauge covariance is unchanged when only the recorded support is enlarged. -/
theorem GaugeCovariantAt.enlarge
    (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ)) (hPhi : GaugeCovariantAt rho x Phi)
    (S : Finset (PositiveEdge d)) (hS : Phi.support ⊆ S) :
    GaugeCovariantAt rho x (Phi.enlarge S hS) := by
  intro g A
  simpa using hPhi g A

/-- Translation pullback moves the base site and preserves endpoint gauge
covariance.  This is the basic constructor for the translated endpoint family
used by straight screened lines. -/
theorem GaugeCovariantAt.translatePullback
    (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ)) (hPhi : GaugeCovariantAt rho x Phi)
    (v : Site d) :
    GaugeCovariantAt rho (Lattice.Cubic.translate v x)
      (Phi.translatePullback v) := by
  intro g A
  rw [LocalField.translatePullback_apply, LocalField.translatePullback_apply]
  have hcov : LocalObservable.translateConfiguration v (gaugeTransform g A) =
      gaugeTransform (fun z => g (Lattice.Cubic.translate v z))
        (LocalObservable.translateConfiguration v A) := by
    funext e
    simp only [LocalObservable.translateConfiguration, gaugeTransform_apply,
      PositiveEdge.source_translate, PositiveEdge.target_translate]
  rw [hcov, hPhi]

section EquivariantPostcomp

variable {m : ℕ}

/-- Postcompose a coordinate endpoint field by a continuous linear map. -/
def LocalField.postcompLinear
    (Phi : LocalField d G (Fin n → ℂ))
    (T : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) :
    LocalField d G (Fin m → ℂ) :=
  Phi.postcomp ⟨T, T.continuous⟩

omit [Group G] in
@[simp]
theorem LocalField.postcompLinear_apply
    (Phi : LocalField d G (Fin n → ℂ))
    (T : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ))
    (A : Configuration d G) :
    Phi.postcompLinear T A = T (Phi A) :=
  rfl

/-- An equivariant continuous linear image of a covariant local field is a
covariant local field.  This is the abstract endpoint-construction hook used
for the screening intertwiner. -/
theorem GaugeCovariantAt.postcompLinear
    (rho : ContinuousUnitaryRepData G n)
    (tau : ContinuousUnitaryRepData G m) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : GaugeCovariantAt rho x Phi)
    (T : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ))
    (hT : ∀ g v, T (representationAction rho g v) =
      representationAction tau g (T v)) :
    GaugeCovariantAt tau x (Phi.postcompLinear T) := by
  intro g A
  rw [LocalField.postcompLinear_apply, LocalField.postcompLinear_apply,
    hPhi g A, hT]

omit [Group G] in
/-- A witnessed nonzero endpoint value survives any continuous linear map
that does not kill that witness. -/
theorem LocalField.postcompLinear_ne_at
    (Phi : LocalField d G (Fin n → ℂ))
    (T : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ))
    (A : Configuration d G) (h : T (Phi A) ≠ 0) :
    Phi.postcompLinear T A ≠ 0 := by
  simpa using h

end EquivariantPostcomp

end

end YangMills.Gluelump.Endpoint
