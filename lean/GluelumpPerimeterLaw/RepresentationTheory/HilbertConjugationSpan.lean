/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.ConjugationSpan
import GluelumpPerimeterLaw.RepresentationTheory.CoordinateUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hilbert--Schmidt model of the conjugation span

The ordinary `Matrix` type carries the finite-product supremum norm, which is
not the norm of its entrywise Hermitian inner product.  We therefore transport
the literal matrix conjugation span to a nested `PiLp 2` copy.  This retains
the exact span of the matrices `sigma(g)` while giving it the genuine
Hilbert--Schmidt inner product required by the unitary-coordinate adapter.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson WithLp
open scoped Matrix InnerProductSpace

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {n : ℕ}

/-- Matrices with their entrywise `L²`, hence Hilbert--Schmidt, geometry. -/
abbrev HilbertMatrix (n : ℕ) :=
  PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin n => ℂ))

/-- The coordinate-preserving linear equivalence from ordinary matrices to
their Hilbert--Schmidt copy. -/
def matrixHilbertEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] HilbertMatrix n where
  toFun A := toLp 2 (fun i => toLp 2 (A i))
  invFun A := fun i j => A i j
  left_inv _ := rfl
  right_inv A := by
    apply PiLp.ext
    intro i
    apply PiLp.ext
    intro j
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem matrixHilbertEquiv_apply (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : matrixHilbertEquiv n A i j = A i j :=
  rfl

@[simp]
theorem matrixHilbertEquiv_symm_apply (A : HilbertMatrix n)
    (i j : Fin n) : (matrixHilbertEquiv n).symm A i j = A i j :=
  rfl

/-- The literal conjugation span inside Hilbert--Schmidt matrix coordinates. -/
def HilbertConjSpan (sigma : ContinuousUnitaryRepData G n) :
    Submodule ℂ (HilbertMatrix n) :=
  (ConjSpan sigma).map (matrixHilbertEquiv n).toLinearMap

/-- The literal and Hilbert--Schmidt copies of the conjugation span are
canonically linearly equivalent. -/
def conjSpanHilbertEquiv (sigma : ContinuousUnitaryRepData G n) :
    ConjSpan sigma ≃ₗ[ℂ] HilbertConjSpan sigma :=
  Submodule.equivMapOfInjective (matrixHilbertEquiv n).toLinearMap
    (matrixHilbertEquiv n).injective (ConjSpan sigma)

@[simp]
theorem conjSpanHilbertEquiv_apply_coe
    (sigma : ContinuousUnitaryRepData G n) (A : ConjSpan sigma)
    (i j : Fin n) :
    (conjSpanHilbertEquiv sigma A : HilbertMatrix n) i j = A.1 i j :=
  by
    change matrixHilbertEquiv n A.1 i j = A.1 i j
    rfl

@[simp]
theorem conjSpanHilbertEquiv_symm_apply_coe
    (sigma : ContinuousUnitaryRepData G n) (A : HilbertConjSpan sigma)
    (i j : Fin n) :
    ((conjSpanHilbertEquiv sigma).symm A :
      Matrix (Fin n) (Fin n) ℂ) i j = A.1 i j :=
  by
    have h : matrixHilbertEquiv n
        ((conjSpanHilbertEquiv sigma).symm A).1 = A.1 :=
      Submodule.map_equivMapOfInjective_symm_apply
      (matrixHilbertEquiv n).toLinearMap
      (matrixHilbertEquiv n).injective (ConjSpan sigma) A
    exact congrArg (fun X : HilbertMatrix n => X i j) h

@[simp]
theorem matrixHilbertEquiv_symm_coe_eq_conjSpanHilbertEquiv_symm
    (sigma : ContinuousUnitaryRepData G n) (A : HilbertConjSpan sigma) :
    (matrixHilbertEquiv n).symm A.1 =
      ((conjSpanHilbertEquiv sigma).symm A).1 := by
  ext i j
  exact (conjSpanHilbertEquiv_symm_apply_coe sigma A i j).symm

/-- Transport the literal conjugation action to its Hilbert--Schmidt copy. -/
def hilbertConjSpanRep (sigma : ContinuousUnitaryRepData G n) :
    Representation ℂ G (HilbertConjSpan sigma) where
  toFun g := (conjSpanHilbertEquiv sigma).toLinearMap.comp
    ((conjSpanRep sigma g).comp
      (conjSpanHilbertEquiv sigma).symm.toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro A
    change conjSpanHilbertEquiv sigma
      (conjSpanRep sigma 1 ((conjSpanHilbertEquiv sigma).symm A)) = A
    simpa using (conjSpanHilbertEquiv sigma).apply_symm_apply A
  map_mul' g h := by
    apply LinearMap.ext
    intro A
    change conjSpanHilbertEquiv sigma
        (conjSpanRep sigma (g * h) ((conjSpanHilbertEquiv sigma).symm A)) = _
    rw [map_mul, Module.End.mul_apply]
    simp

/-- The transport equivalence is equivariant by construction. -/
def conjSpanHilbertRepEquiv (sigma : ContinuousUnitaryRepData G n) :
    (conjSpanRep sigma).Equiv (hilbertConjSpanRep sigma) where
  toLinearEquiv := conjSpanHilbertEquiv sigma
  isIntertwining' g := by
    apply LinearMap.ext
    intro A
    change conjSpanHilbertEquiv sigma (conjSpanRep sigma g A) = _
    simp [hilbertConjSpanRep]

@[simp]
theorem conjSpanHilbertEquiv_symm_hilbertConjSpanRep
    (sigma : ContinuousUnitaryRepData G n) (g : G)
    (A : HilbertConjSpan sigma) :
    (conjSpanHilbertEquiv sigma).symm (hilbertConjSpanRep sigma g A) =
      conjSpanRep sigma g ((conjSpanHilbertEquiv sigma).symm A) := by
  apply (conjSpanHilbertEquiv sigma).injective
  simp [hilbertConjSpanRep]

/-- The Hilbert--Schmidt inner product is the trace of `Aᴴ B`. -/
theorem hilbertMatrix_inner_eq_trace (A B : HilbertMatrix n) :
    ⟪A, B⟫_ℂ = Matrix.trace
      (((matrixHilbertEquiv n).symm A)ᴴ *
        (matrixHilbertEquiv n).symm B) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, matrixHilbertEquiv_symm_apply]
  rw [Finset.sum_comm]

/-- Conjugation commutes with conjugate transpose on the literal span. -/
theorem conjSpanRep_conjTranspose
    (sigma : ContinuousUnitaryRepData G n) (g : G) (A : ConjSpan sigma) :
    (conjSpanRep sigma g A).1ᴴ =
      (conjSpanRep sigma g
        ⟨A.1ᴴ, conjTranspose_mem_conjSpan sigma A.2⟩).1 := by
  simp only [conjSpanRep_apply_coe, Matrix.conjTranspose_mul,
    map_inv, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Conjugation preserves the Hilbert--Schmidt inner product. -/
theorem hilbertConjSpanRep_inner
    (sigma : ContinuousUnitaryRepData G n) (g : G)
    (A B : HilbertConjSpan sigma) :
    ⟪hilbertConjSpanRep sigma g A,
        hilbertConjSpanRep sigma g B⟫_ℂ = ⟪A, B⟫_ℂ := by
  let A' := (conjSpanHilbertEquiv sigma).symm A
  let B' := (conjSpanHilbertEquiv sigma).symm B
  change ⟪(hilbertConjSpanRep sigma g A : HilbertMatrix n),
      (hilbertConjSpanRep sigma g B : HilbertMatrix n)⟫_ℂ =
    ⟪(A : HilbertMatrix n), (B : HilbertMatrix n)⟫_ℂ
  rw [hilbertMatrix_inner_eq_trace, hilbertMatrix_inner_eq_trace]
  simp only [matrixHilbertEquiv_symm_coe_eq_conjSpanHilbertEquiv_symm,
    conjSpanHilbertEquiv_symm_hilbertConjSpanRep]
  change Matrix.trace ((conjSpanRep sigma g A').1ᴴ *
      (conjSpanRep sigma g B').1) = Matrix.trace (A'.1ᴴ * B'.1)
  rw [conjSpanRep_conjTranspose]
  exact conjSpanTracePairing_invariant sigma g
    ⟨A'.1ᴴ, conjTranspose_mem_conjSpan sigma A'.2⟩ B'

/-- Every orbit in the Hilbert conjugation span is continuous. -/
theorem continuous_hilbertConjSpanRep
    (sigma : ContinuousUnitaryRepData G n)
    (A : HilbertConjSpan sigma) :
    Continuous (fun g => hilbertConjSpanRep sigma g A) := by
  let A' := (conjSpanHilbertEquiv sigma).symm A
  apply (conjSpanHilbertEquiv sigma).toLinearMap.continuous_of_finiteDimensional.comp
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  change Continuous (fun g =>
    ((sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) * A'.1 *
      (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ)) i j)
  exact (((continuous_subtype_val.comp sigma.continuous_ρ).matrix_mul
    continuous_const).matrix_mul
      (continuous_subtype_val.comp
        (sigma.continuous_ρ.comp continuous_inv))).matrix_elem i j

/-- The span is nontrivial because it contains the nonzero identity matrix. -/
instance hilbertConjSpan_nontrivial
    (sigma : ContinuousUnitaryRepData G n) :
    Nontrivial (HilbertConjSpan sigma) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp sigma.dimension_pos
  refine ⟨⟨0, conjSpanHilbertEquiv sigma
    ⟨1, one_mem_conjSpan sigma⟩, ?_⟩⟩
  intro h
  have h' := congrArg (conjSpanHilbertEquiv sigma).symm h
  simp only [map_zero, LinearEquiv.symm_apply_apply] at h'
  exact one_ne_zero (congrArg Subtype.val h').symm

/-- Fixed orthonormal coordinates together with their equivariant comparison
to the literal conjugation span.  Packaging the two together ensures that the
representation appearing in the equivalence is definitionally the same
object as the first projection. -/
def hilbertConjSpanCoordinateModel
    (sigma : ContinuousUnitaryRepData G n) :
    Σ rho : ContinuousUnitaryRepData G
      (Module.finrank ℂ (HilbertConjSpan sigma)),
      (asRepresentation rho).Equiv (conjSpanRep sigma) := by
  letI normed : NormedAddCommGroup (HilbertConjSpan sigma) := inferInstance
  letI inner : InnerProductSpace ℂ (HilbertConjSpan sigma) := inferInstance
  letI finite : FiniteDimensional ℂ (HilbertConjSpan sigma) := inferInstance
  letI nontrivial : Nontrivial (HilbertConjSpan sigma) := inferInstance
  let model := @coordinateUnitaryRepModel G (HilbertConjSpan sigma)
      _ _ normed inner finite nontrivial
      (hilbertConjSpanRep sigma)
      (continuous_hilbertConjSpanRep (G := G) (n := n) sigma)
      (hilbertConjSpanRep_inner (G := G) (n := n) sigma)
  exact ⟨model.1, model.2.trans
    (conjSpanHilbertRepEquiv (G := G) (n := n) sigma).symm⟩

/-- The fixed matrix representation supplied by the coordinate model. -/
def hilbertConjSpanUnitaryRepData
    (sigma : ContinuousUnitaryRepData G n) :
    ContinuousUnitaryRepData G
      (Module.finrank ℂ (HilbertConjSpan sigma)) :=
  (hilbertConjSpanCoordinateModel sigma).1

/-- The coordinate model is equivariantly equivalent to the literal
conjugation span. -/
def hilbertConjSpanCoordinateEquiv
    (sigma : ContinuousUnitaryRepData G n) :
    (asRepresentation (hilbertConjSpanUnitaryRepData sigma)).Equiv
      (conjSpanRep sigma) :=
  (hilbertConjSpanCoordinateModel sigma).2

end

end YangMills.Gluelump.RepresentationTheory
