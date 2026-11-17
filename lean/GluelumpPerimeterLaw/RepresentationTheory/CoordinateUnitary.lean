/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Orthonormal coordinates for finite-dimensional unitary representations

This adapter puts an abstract finite-dimensional continuous unitary action in
the fixed matrix coordinates used by the Wilson and Stone--Weierstrass layers.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson
open scoped Matrix InnerProductSpace

noncomputable section

variable {G V : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [Nontrivial V]

/-- A group representation operator as a linear equivalence. -/
def representationLinearEquiv (rho : Representation ℂ G V) (g : G) : V ≃ₗ[ℂ] V where
  toLinearMap := rho g
  invFun := rho g⁻¹
  left_inv x := by
    change rho g⁻¹ (rho g x) = x
    simpa [← Module.End.mul_apply, ← map_mul]
  right_inv x := by
    change rho g (rho g⁻¹ x) = x
    simpa [← Module.End.mul_apply, ← map_mul]

/-- The preceding equivalence as a linear isometry, assuming preservation of
the Hermitian inner product. -/
def representationLinearIsometryEquiv (rho : Representation ℂ G V)
    (hunitary : ∀ g x y, ⟪rho g x, rho g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) :
    V ≃ₗᵢ[ℂ] V :=
  (representationLinearEquiv rho g).isometryOfInner (by
    intro x y
    exact hunitary g x y)

/-- Fixed orthonormal matrix coordinates for an abstract representation. -/
def coordinateUnitaryRepData (rho : Representation ℂ G V)
    (hcontinuous : ∀ v, Continuous fun g => rho g v)
    (hunitary : ∀ g x y, ⟪rho g x, rho g y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ContinuousUnitaryRepData G (Module.finrank ℂ V) where
  ρ := {
    toFun := fun g => ⟨LinearMap.toMatrix
        (stdOrthonormalBasis ℂ V).toBasis
        (stdOrthonormalBasis ℂ V).toBasis (rho g), by
      simpa [representationLinearIsometryEquiv,
        LinearEquiv.isometryOfInner_toLinearEquiv] using
        (representationLinearIsometryEquiv rho hunitary g).toMatrix_mem_unitaryGroup
          (stdOrthonormalBasis ℂ V) (stdOrthonormalBasis ℂ V)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' g h := by
      apply Subtype.ext
      simp [LinearMap.toMatrix_mul] }
  continuous_ρ := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    rw [show (fun g => LinearMap.toMatrix
        (stdOrthonormalBasis ℂ V).toBasis
        (stdOrthonormalBasis ℂ V).toBasis (rho g) i j) =
      fun g => ((stdOrthonormalBasis ℂ V).toBasis.repr
        (rho g ((stdOrthonormalBasis ℂ V) j))) i by
      funext g
      exact LinearMap.toMatrix_apply _ _ _ _ _]
    let phi : Module.Dual ℂ V :=
      (Finsupp.lapply i).comp
        (stdOrthonormalBasis ℂ V).toBasis.repr.toLinearMap
    exact phi.continuous_of_finiteDimensional.comp
      (hcontinuous ((stdOrthonormalBasis ℂ V) j))
  dimension_pos := Module.finrank_pos

/-- The coordinate representation is equivariantly equivalent to the
original abstract representation. -/
def coordinateUnitaryRepEquiv (rho : Representation ℂ G V)
    (hcontinuous : ∀ v, Continuous fun g => rho g v)
    (hunitary : ∀ g x y, ⟪rho g x, rho g y⟫_ℂ = ⟪x, y⟫_ℂ) :
    (asRepresentation (coordinateUnitaryRepData rho hcontinuous hunitary)).Equiv rho where
  toLinearEquiv := (stdOrthonormalBasis ℂ V).toBasis.equivFun.symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    let b := (stdOrthonormalBasis ℂ V).toBasis
    simp only [LinearMap.comp_apply, asRepresentation_apply]
    apply b.equivFun.injective
    change b.equivFun (b.equivFun.symm
        (((coordinateUnitaryRepData rho hcontinuous hunitary).ρ g :
          Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ) *ᵥ x)) =
      b.equivFun (rho g (b.equivFun.symm x))
    rw [b.equivFun.apply_symm_apply]
    change LinearMap.toMatrix b b (rho g) *ᵥ x =
      b.equivFun (rho g (b.equivFun.symm x))
    ext i
    have h := congrFun
      (LinearMap.toMatrix_mulVec_repr b b (rho g) (b.equivFun.symm x)) i
    have hx : (⇑(b.repr (b.equivFun.symm x)) :
        Fin (Module.finrank ℂ V) → ℂ) = x :=
      b.equivFun.apply_symm_apply x
    rw [hx] at h
    exact h

/-- A coordinate representation bundled with the equivariant equivalence that
identifies it with the original action.  This package is useful when clients
must retain both objects without asking the elaborator to compare two large
specialized coordinate constructions. -/
def coordinateUnitaryRepModel (rho : Representation ℂ G V)
    (hcontinuous : ∀ v, Continuous fun g => rho g v)
    (hunitary : ∀ g x y, ⟪rho g x, rho g y⟫_ℂ = ⟪x, y⟫_ℂ) :
    Σ data : ContinuousUnitaryRepData G (Module.finrank ℂ V),
      (asRepresentation data).Equiv rho :=
  ⟨coordinateUnitaryRepData rho hcontinuous hunitary,
    coordinateUnitaryRepEquiv rho hcontinuous hunitary⟩

end

end YangMills.Gluelump.RepresentationTheory
