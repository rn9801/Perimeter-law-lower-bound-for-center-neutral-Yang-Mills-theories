/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix

/-!
# A matrix axial map

For a finite continuous unitary representation `eta`, the odd part

`a(g) = (eta(g) - eta(g⁻¹)) / 2`

is continuous and transforms by conjugation.  This is the representation-level
form of the roadmap's adjoint-valued axial map; the genuine Lie-algebra
specialization can later identify its range with the complexified adjoint
module.
-/

namespace YangMills.Gluelump.Lie

open YangMills.Wilson
open scoped Matrix

noncomputable section

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The odd part of a unitary representation matrix. -/
def axialMatrix (eta : ContinuousUnitaryRepData G n) (g : G) :
    Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ)⁻¹ •
    ((eta.ρ g : Matrix (Fin n) (Fin n) ℂ) -
      (eta.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ))

omit [IsTopologicalGroup G] in
/-- The matrix axial map vanishes at the identity. -/
@[simp]
theorem axialMatrix_one (eta : ContinuousUnitaryRepData G n) :
    axialMatrix eta 1 = 0 := by
  simp [axialMatrix]

omit [IsTopologicalGroup G] in
/-- The axial map is odd under inversion. -/
theorem axialMatrix_inv (eta : ContinuousUnitaryRepData G n) (g : G) :
    axialMatrix eta g⁻¹ = -axialMatrix eta g := by
  simp only [axialMatrix, inv_inv]
  module

/-- Continuity of the axial map. -/
theorem continuous_axialMatrix (eta : ContinuousUnitaryRepData G n) :
    Continuous (axialMatrix eta) := by
  unfold axialMatrix
  have hρ : Continuous fun g : G =>
      (eta.ρ g : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp eta.continuous_ρ
  have hρinv : Continuous fun g : G =>
      (eta.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) :=
    hρ.comp continuous_inv
  fun_prop

omit [IsTopologicalGroup G] in
/-- Conjugation covariance of the axial map. -/
theorem axialMatrix_conj (eta : ContinuousUnitaryRepData G n) (h g : G) :
    axialMatrix eta (h * g * h⁻¹) =
      (eta.ρ h : Matrix (Fin n) (Fin n) ℂ) * axialMatrix eta g *
        (eta.ρ h⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [axialMatrix, map_mul, map_inv, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, mul_inv_rev, inv_inv]
  noncomm_ring

omit [IsTopologicalGroup G] in
/-- A witness on which the representation distinguishes `g` from `g⁻¹`
makes the axial map nonzero. -/
theorem axialMatrix_ne_zero (eta : ContinuousUnitaryRepData G n) {g : G}
    (hg : (eta.ρ g : Matrix (Fin n) (Fin n) ℂ) ≠
      (eta.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :
    axialMatrix eta g ≠ 0 := by
  intro hzero
  have hscalar : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
  have hdiff : (eta.ρ g : Matrix (Fin n) (Fin n) ℂ) -
      (eta.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) = 0 :=
    (smul_eq_zero.mp (by simpa [axialMatrix] using hzero)).resolve_left hscalar
  exact hg (sub_eq_zero.mp hdiff)

end

end YangMills.Gluelump.Lie
