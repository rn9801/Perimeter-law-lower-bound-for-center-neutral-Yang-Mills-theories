/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.CenterQuotientUnitary
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Fixed unitary coordinates for algebraic dual representations
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson
open scoped Matrix ComplexConjugate

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {n : ℕ}

/-- Entrywise conjugation gives the fixed matrix model of the contragredient
of a unitary representation. -/
def dualUnitaryRepData (rho : ContinuousUnitaryRepData G n) :
    ContinuousUnitaryRepData G n where
  ρ := {
    toFun := fun g => Matrix.UnitaryGroup.map_star (rho.ρ g)
    map_one' := by
      apply Subtype.ext
      ext i j
      simp [Matrix.UnitaryGroup.map_star]
    map_mul' g h := by
      apply Subtype.ext
      ext i j
      simp only [map_mul, Matrix.UnitaryGroup.map_star,
        Matrix.UnitaryGroup.mul_val, Matrix.map_apply, map_mul,
        Matrix.mul_apply, Complex.star_def, map_sum] }
  continuous_ρ := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    exact continuous_star.comp
      (((continuous_subtype_val.comp rho.continuous_ρ).matrix_elem i j))
  dimension_pos := rho.dimension_pos

@[simp]
theorem dualUnitaryRepData_apply
    (rho : ContinuousUnitaryRepData G n) (g : G) (i j : Fin n) :
    ((dualUnitaryRepData rho).ρ g : Matrix (Fin n) (Fin n) ℂ) i j =
      star ((rho.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) :=
  rfl

/-- Standard coordinates on the algebraic dual. -/
def standardDualCoordinates (n : ℕ) :
    Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun

@[simp]
theorem standardDualCoordinates_apply
    (f : Module.Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    standardDualCoordinates n f i = f (Pi.single i 1) := by
  simp [standardDualCoordinates]

/-- The standard coordinates of the algebraic dual action are entrywise
conjugate unitary matrices. -/
theorem standardDualCoordinates_action
    (rho : ContinuousUnitaryRepData G n) (g : G)
    (f : Module.Dual ℂ (Fin n → ℂ)) :
    standardDualCoordinates n ((asRepresentation rho).dual g f) =
      asRepresentation (dualUnitaryRepData rho) g
        (standardDualCoordinates n f) := by
  ext i
  simp only [standardDualCoordinates_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply,
    asRepresentation_apply, Matrix.mulVec, dotProduct,
    dualUnitaryRepData_apply]
  let v₀ : Fin n → ℂ :=
    (rho.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ).mulVec (Pi.single i 1)
  have hvec : v₀ = ∑ j, v₀ j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  change f v₀ = ∑ x, star ((rho.ρ g : Matrix _ _ ℂ) i x) *
    f (Pi.single x 1)
  rw [hvec, map_sum]
  simp [v₀, Matrix.mulVec, Pi.single_apply, map_smul, map_inv,
    Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose, mul_comm]

/-- The fixed entrywise-conjugate model is equivariantly equivalent to the
algebraic dual representation. -/
def dualUnitaryRepEquiv (rho : ContinuousUnitaryRepData G n) :
    (asRepresentation (dualUnitaryRepData rho)).Equiv
      (asRepresentation rho).dual :=
  (Representation.Equiv.mk (standardDualCoordinates n)
    (fun g => by
      apply LinearMap.ext
      intro f
      exact standardDualCoordinates_action rho g f)).symm

end

end YangMills.Gluelump.RepresentationTheory
