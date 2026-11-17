/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.Center
import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The conjugation span of a unitary matrix representation

For a fixed-coordinate unitary representation `sigma`, `ConjSpan sigma` is
the complex linear span of the actual matrices `sigma(g)`.  This is the
screening source in the all-coupling gluelump construction; using the span,
rather than all endomorphisms, is essential for the later pure-holonomy
nonvanishing argument.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson
open scoped Matrix

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- Complex span of the matrices in the image of `sigma`. -/
def ConjSpan (sigma : ContinuousUnitaryRepData G n) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Submodule.span ℂ (Set.range fun g : G =>
    (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ))

/-- Every actual representation matrix belongs to its conjugation span. -/
theorem sigma_mem_conjSpan (sigma : ContinuousUnitaryRepData G n) (g : G) :
    (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) ∈ ConjSpan sigma :=
  Submodule.subset_span (Set.mem_range_self g)

/-- The identity matrix belongs to the conjugation span. -/
theorem one_mem_conjSpan (sigma : ContinuousUnitaryRepData G n) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ ConjSpan sigma := by
  simpa using sigma_mem_conjSpan sigma 1

/-- The conjugate transpose of an element of the conjugation span remains in
the conjugation span.  On generators this is just unitarity:
`sigma(g)ᴴ = sigma(g⁻¹)`. -/
theorem conjTranspose_mem_conjSpan (sigma : ContinuousUnitaryRepData G n)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ ConjSpan sigma) :
    Aᴴ ∈ ConjSpan sigma := by
  refine Submodule.span_induction (p := fun X _ => Xᴴ ∈ ConjSpan sigma)
    ?_ ?_ ?_ ?_ hA
  · rintro X ⟨g, rfl⟩
    simpa only [map_inv, Matrix.UnitaryGroup.inv_val,
      Matrix.star_eq_conjTranspose] using sigma_mem_conjSpan sigma g⁻¹
  · simp
  · intro X Y _ _ hX hY
    simpa using (ConjSpan sigma).add_mem hX hY
  · intro c X _ hX
    simpa using (ConjSpan sigma).smul_mem (star c) hX

/-- Conjugation by `sigma(g)` as a linear map on the full matrix algebra. -/
def conjugateMatrixLinearMap (sigma : ContinuousUnitaryRepData G n) (g : G) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.mulLeftRight ℂ
    ((sigma.ρ g : Matrix (Fin n) (Fin n) ℂ),
      (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ))

/-- The span of representation matrices is stable under conjugation. -/
theorem conjugate_mem_conjSpan (sigma : ContinuousUnitaryRepData G n)
    (g : G) {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ ConjSpan sigma) :
    conjugateMatrixLinearMap sigma g A ∈ ConjSpan sigma := by
  refine Submodule.span_induction (p := fun X _ =>
    conjugateMatrixLinearMap sigma g X ∈ ConjSpan sigma) ?_ ?_ ?_ ?_ hA
  · rintro X ⟨h, rfl⟩
    change (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) *
        (sigma.ρ h : Matrix (Fin n) (Fin n) ℂ) *
        (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) ∈ ConjSpan sigma
    simpa only [map_mul, Matrix.UnitaryGroup.mul_val] using
      sigma_mem_conjSpan sigma (g * h * g⁻¹)
  · simp [conjugateMatrixLinearMap]
  · intro X Y _ _ hX hY
    simpa only [map_add] using (ConjSpan sigma).add_mem hX hY
  · intro c X _ hX
    simpa only [map_smul] using (ConjSpan sigma).smul_mem c hX

/-- Conjugation by `sigma` restricted to `ConjSpan sigma`. -/
def conjSpanRep (sigma : ContinuousUnitaryRepData G n) :
    Representation ℂ G (ConjSpan sigma) where
  toFun g := {
    toFun := fun A =>
      ⟨conjugateMatrixLinearMap sigma g A,
        conjugate_mem_conjSpan sigma g A.2⟩
    map_add' := by intro A B; apply Subtype.ext; simp
    map_smul' := by intro c A; apply Subtype.ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro A
    apply Subtype.ext
    simp [conjugateMatrixLinearMap]
  map_mul' g h := by
    apply LinearMap.ext
    intro A
    apply Subtype.ext
    simp [conjugateMatrixLinearMap, Module.End.mul_apply]
    noncomm_ring

@[simp]
theorem conjSpanRep_apply_coe (sigma : ContinuousUnitaryRepData G n)
    (g : G) (A : ConjSpan sigma) :
    (conjSpanRep sigma g A : Matrix (Fin n) (Fin n) ℂ) =
      (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) * A.1 *
        (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) :=
  rfl

/-- A faithful matrix representation has exactly the center as the kernel of
its conjugation action on the literal span of its matrices. -/
theorem conjSpanRep_kernelIsCenter (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) :
    KernelIsCenter (conjSpanRep sigma) := by
  intro g
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro h
    have happ := LinearMap.congr_fun hg
      (⟨(sigma.ρ h : Matrix (Fin n) (Fin n) ℂ),
        sigma_mem_conjSpan sigma h⟩ : ConjSpan sigma)
    have hmatrix :
        (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) *
            (sigma.ρ h : Matrix (Fin n) (Fin n) ℂ) *
            (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) =
          (sigma.ρ h : Matrix (Fin n) (Fin n) ℂ) := by
      exact congrArg Subtype.val happ
    have hconj : g * h * g⁻¹ = h := by
      apply hsigma
      apply Subtype.ext
      simpa only [map_mul, Matrix.UnitaryGroup.mul_val] using hmatrix
    calc
      h * g = (g * h * g⁻¹) * g := by rw [hconj]
      _ = g * h := by group
  · intro hg
    apply LinearMap.ext
    intro A
    apply Subtype.ext
    refine Submodule.span_induction (p := fun X _ =>
      (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) * X *
          (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) = X)
      ?_ ?_ ?_ ?_ A.2
    · rintro X ⟨h, rfl⟩
      have hcomm : h * g = g * h :=
        Subgroup.mem_center_iff.mp hg h
      have hconj : g * h * g⁻¹ = h := by
        rw [← hcomm]
        group
      have hmatrix := congrArg
        (fun k : G => (sigma.ρ k : Matrix (Fin n) (Fin n) ℂ)) hconj
      simpa only [map_mul, Matrix.UnitaryGroup.mul_val] using hmatrix
    · simp
    · intro X Y _ _ hX hY
      simp only [Matrix.mul_add, Matrix.add_mul, hX, hY]
    · intro c X _ hX
      simp only [Matrix.mul_smul, Matrix.smul_mul, hX]

/-- Pointwise kernel equality, in the subgroup-membership form convenient for
quotient descent. -/
theorem conjSpanRep_eq_id_iff_mem_center
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) (g : G) :
    conjSpanRep sigma g = LinearMap.id ↔ g ∈ Subgroup.center G :=
  conjSpanRep_kernelIsCenter sigma hsigma g

/-- Complex-bilinear trace pairing on the conjugation span. -/
def conjSpanTraceToDual (sigma : ContinuousUnitaryRepData G n) :
    ConjSpan sigma →ₗ[ℂ] Module.Dual ℂ (ConjSpan sigma) where
  toFun A := {
    toFun := fun B => Matrix.trace (A.1 * B.1)
    map_add' := by intro B C; simp [Matrix.mul_add]
    map_smul' := by intro c B; simp [Matrix.mul_smul] }
  map_add' A B := by
    ext C
    simp [Matrix.add_mul]
  map_smul' c A := by
    ext B
    simp [Matrix.smul_mul]

@[simp]
theorem conjSpanTraceToDual_apply (sigma : ContinuousUnitaryRepData G n)
    (A B : ConjSpan sigma) :
    conjSpanTraceToDual sigma A B = Matrix.trace (A.1 * B.1) :=
  rfl

/-- Simultaneous conjugation preserves the trace pairing. -/
theorem conjSpanTracePairing_invariant
    (sigma : ContinuousUnitaryRepData G n) (g : G)
    (A B : ConjSpan sigma) :
    conjSpanTraceToDual sigma (conjSpanRep sigma g A)
        (conjSpanRep sigma g B) =
      conjSpanTraceToDual sigma A B := by
  change Matrix.trace
      (((sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) * A.1 *
          (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *
        ((sigma.ρ g : Matrix (Fin n) (Fin n) ℂ) * B.1 *
          (sigma.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ))) =
    Matrix.trace (A.1 * B.1)
  let S : Matrix (Fin n) (Fin n) ℂ := sigma.ρ g
  let I : Matrix (Fin n) (Fin n) ℂ := sigma.ρ g⁻¹
  have hIS : I * S = 1 := by
    dsimp [I, S]
    rw [← Matrix.UnitaryGroup.mul_val, ← map_mul]
    simp
  change Matrix.trace ((S * A.1 * I) * (S * B.1 * I)) =
    Matrix.trace (A.1 * B.1)
  calc
    _ = Matrix.trace (S * (A.1 * B.1) * I) := by
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc I S (B.1 * I), hIS, one_mul]
    _ = Matrix.trace (I * S * (A.1 * B.1)) :=
      Matrix.trace_mul_cycle S (A.1 * B.1) I
    _ = _ := by rw [hIS, one_mul]

/-- The trace pairing is nondegenerate on the conjugation span. -/
theorem conjSpanTraceToDual_injective
    (sigma : ContinuousUnitaryRepData G n) :
    Function.Injective (conjSpanTraceToDual sigma) := by
  have hzero : ∀ A : ConjSpan sigma,
      conjSpanTraceToDual sigma A = 0 → A = 0 := by
    intro A hA
    apply Subtype.ext
    have hvalue := LinearMap.congr_fun hA
      (⟨A.1ᴴ, conjTranspose_mem_conjSpan sigma A.2⟩ : ConjSpan sigma)
    have htrace : Matrix.trace (A.1 * A.1ᴴ) = 0 := by
      simpa using hvalue
    have hsum : (∑ i : Fin n, ∑ j : Fin n,
        Complex.normSq (A.1 i j)) = 0 := by
      have hre := congrArg Complex.re htrace
      simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.mul_conj] using hre
    have hentry : ∀ i j : Fin n, Complex.normSq (A.1 i j) = 0 := by
      intro i j
      have hi : (∑ j : Fin n, Complex.normSq (A.1 i j)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => Finset.sum_nonneg fun l _ =>
            Complex.normSq_nonneg (A.1 k l))).mp hsum i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => Complex.normSq_nonneg (A.1 i k))).mp hi j
          (Finset.mem_univ j)
    exact Matrix.ext fun i j => Complex.normSq_eq_zero.mp (hentry i j)
  intro A B hAB
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hAB, sub_self]

/-- Finite dimensionality upgrades nondegeneracy to surjectivity. -/
theorem conjSpanTraceToDual_surjective
    (sigma : ContinuousUnitaryRepData G n) :
    Function.Surjective (conjSpanTraceToDual sigma) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℂ) (V := ConjSpan sigma)).symm).mp
  exact conjSpanTraceToDual_injective sigma

/-- The trace map intertwines conjugation with the algebraic dual action. -/
theorem conjSpanTraceToDual_isIntertwining
    (sigma : ContinuousUnitaryRepData G n) (g : G) (A : ConjSpan sigma) :
    conjSpanTraceToDual sigma (conjSpanRep sigma g A) =
      (conjSpanRep sigma).dual g (conjSpanTraceToDual sigma A) := by
  ext B
  change conjSpanTraceToDual sigma (conjSpanRep sigma g A) B =
    conjSpanTraceToDual sigma A (conjSpanRep sigma g⁻¹ B)
  have hinv := conjSpanTracePairing_invariant sigma g A
    (conjSpanRep sigma g⁻¹ B)
  simpa using hinv

/-- The invariant complex-bilinear trace pairing identifies the conjugation
span representation with its algebraic dual. -/
noncomputable def conjSpanSelfDual (sigma : ContinuousUnitaryRepData G n) :
    (conjSpanRep sigma).Equiv (conjSpanRep sigma).dual where
  toLinearEquiv := LinearEquiv.ofBijective (conjSpanTraceToDual sigma)
    ⟨conjSpanTraceToDual_injective sigma,
      conjSpanTraceToDual_surjective sigma⟩
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro A
    exact conjSpanTraceToDual_isIntertwining sigma g A

end

end YangMills.Gluelump.RepresentationTheory
