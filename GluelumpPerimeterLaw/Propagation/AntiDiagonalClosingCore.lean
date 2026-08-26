/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.AntiDiagonalReflection
import GluelumpPerimeterLaw.Endpoint.RankOne
import YangMills.Wilson.Loop

/-!
# Measure-independent matrix anti-diagonal closing

This file exposes the represented holonomy matrix as a finite scalar family
and proves the exact pointwise mixed and self-pairing identities used by the
second corner reflection.  It contains no Gibbs-state or limit assumptions.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson
open scoped Matrix BigOperators

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- A matrix coefficient of the represented holonomy, with its two indices
flattened canonically. -/
def holonomyMatrixFlattenedComponent
    (rho : ContinuousUnitaryRepData G n) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (a : Fin (n * n)) :
    LocalObservable d G where
  toContinuousMap :=
    ⟨fun A =>
        let ij := finProdFinEquiv.symm a
        (rho.ρ (holonomy A p) : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2,
      ((continuous_apply (finProdFinEquiv.symm a).2).comp
        ((continuous_apply (finProdFinEquiv.symm a).1).comp
          (continuous_subtype_val.comp
            (rho.continuous_ρ.comp (continuous_holonomy p)))))⟩
  support := p.edgeSupport
  dependsOn_support := by
    intro A B hAB
    change (rho.ρ (holonomy A p) : Matrix (Fin n) (Fin n) ℂ)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 =
      (rho.ρ (holonomy B p) : Matrix (Fin n) (Fin n) ℂ)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
    rw [holonomy_eq_of_eqOn_edgeSupport p hAB]

@[simp]
theorem holonomyMatrixFlattenedComponent_apply
    (rho : ContinuousUnitaryRepData G n) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (a : Fin (n * n))
    (A : Configuration d G) :
    holonomyMatrixFlattenedComponent rho p a A =
      (rho.ρ (holonomy A p) : Matrix (Fin n) (Fin n) ℂ)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 :=
  rfl

omit [IsTopologicalGroup G] in
/-- Frobenius contraction of two represented group elements is the character
of their relative product. -/
theorem sum_star_representationMatrix_mul_eq_character
    (rho : ContinuousUnitaryRepData G n) (g h : G) :
    (∑ a : Fin (n * n),
      star ((rho.ρ g : Matrix (Fin n) (Fin n) ℂ)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2) *
      (rho.ρ h : Matrix (Fin n) (Fin n) ℂ)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2) =
      rho.character (g⁻¹ * h) := by
  rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  unfold ContinuousUnitaryRepData.character Matrix.trace Matrix.diag
  simp only [map_mul, map_inv, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, Matrix.mul_apply, Matrix.star_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Cast an anti-diagonally reflected path back to the same fixed endpoints. -/
def antiDiagonalReflectedPathFixed
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y) :
    Lattice.Cubic.Path x y :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (p.antiDiagonalReflect hts k) hx) hy

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem holonomy_antiDiagonalReflectedPathFixed
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y)
    (A : Configuration d G) :
    holonomy A (antiDiagonalReflectedPathFixed hts k p hx hy) =
      holonomy (antiDiagonalReflectConfiguration tau sigma k A) p := by
  unfold antiDiagonalReflectedPathFixed
  rw [holonomy_castTarget, holonomy_castSource,
    holonomy_antiDiagonalReflectConfiguration_path hts]

/-- The matrix-family self-pairing closes the path into a Wilson loop, with
the unnormalized trace contributing exactly the representation dimension. -/
theorem holonomyMatrix_antiDiagonalFamilySelfProduct_apply
    (rho : ContinuousUnitaryRepData G n)
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y)
    (A : Configuration d G) :
    (∑ a : Fin (n * n),
      (holonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        tau sigma k (holonomyMatrixFlattenedComponent rho p a) A) =
      (n : ℂ) * rho.wilsonLoop
        ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A := by
  simp only [LocalObservable.antiDiagonalReflectionProduct_apply,
    holonomyMatrixFlattenedComponent_apply]
  rw [sum_star_representationMatrix_mul_eq_character]
  simp only [ContinuousUnitaryRepData.wilsonLoop_apply, holonomy_comp,
    holonomy_reverse]
  rw [holonomy_antiDiagonalReflectedPathFixed]
  unfold ContinuousUnitaryRepData.normalizedCharacter
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast rho.dimension_pos.ne'
  field_simp

/-- Pairing the reflected transport matrix with the endpoint rank-one matrix
is exactly the screened observable along the reflected path. -/
theorem holonomyMatrix_rankOne_antiDiagonalFamilyProduct_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : Endpoint.LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y)
    (A : Configuration d G) :
    (∑ a : Fin (n * n),
      (holonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        tau sigma k ((Endpoint.rankOneFlattened Phi Psi).component a) A) =
      Endpoint.screenedObservable rho Phi Psi
        (antiDiagonalReflectedPathFixed hts k p hx hy) A := by
  rw [Endpoint.screenedObservable_apply]
  unfold Endpoint.screenedValue Endpoint.dualAction Matrix.mulVec dotProduct
  rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
  simp only [LocalObservable.antiDiagonalReflectionProduct_apply,
    holonomyMatrixFlattenedComponent_apply,
    Endpoint.LocalField.component_apply, Endpoint.rankOneFlattened_apply,
    Equiv.symm_apply_apply, map_inv, Matrix.UnitaryGroup.inv_val,
    Matrix.transpose_apply, Matrix.star_apply,
    holonomy_antiDiagonalReflectedPathFixed, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro j
  ring

/-- Path support gives componentwise support of the full matrix family. -/
theorem holonomyMatrixFlattenedComponent_supportedInAntiDiagonalPositiveHalf
    (rho : ContinuousUnitaryRepData G n) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (tau sigma : Fin d) (k : ℤ)
    (hp : Endpoint.Path.SupportedInAntiDiagonalPositiveHalf tau sigma k p)
    (a : Fin (n * n)) :
    LocalObservable.SupportedInAntiDiagonalPositiveHalf tau sigma k
      (holonomyMatrixFlattenedComponent rho p a) :=
  hp

end

end YangMills.Gluelump.Propagation
