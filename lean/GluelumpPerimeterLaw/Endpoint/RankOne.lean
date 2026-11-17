/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ReflectionSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Rank-one endpoint matrices

The second corner in the gluelump argument compares the transported holonomy
matrix with the rank-one matrix formed from its two endpoint vectors.  This
file keeps both matrix indices until the reflection pairing, flattening them
only through the canonical equivalence `Fin m × Fin n ≃ Fin (m * n)`.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

variable {d m n : ℕ} {G : Type*} [TopologicalSpace G]

/-- The flattened rank-one matrix `Phiᴴ Psi`, with entries
`conj (Phi i) * Psi j`.  Its recorded support is the union of the two endpoint
collars. -/
def rankOneFlattened
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ)) :
    LocalField d G (Fin (m * n) → ℂ) where
  toContinuousMap :=
    ⟨fun A a =>
        let ij := finProdFinEquiv.symm a
        star (Phi A ij.1) * Psi A ij.2,
      continuous_pi fun a => by
        exact (continuous_star.comp
          ((continuous_apply (finProdFinEquiv.symm a).1).comp
            Phi.toContinuousMap.continuous)).mul
          ((continuous_apply (finProdFinEquiv.symm a).2).comp
            Psi.toContinuousMap.continuous)⟩
  support := Phi.support ∪ Psi.support
  dependsOn_support := by
    intro A B hAB
    have hPhi : Phi A = Phi B := Phi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_left _ he)
    have hPsi : Psi A = Psi B := Psi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_right _ he)
    funext a
    change star (Phi A (finProdFinEquiv.symm a).1) *
        Psi A (finProdFinEquiv.symm a).2 =
      star (Phi B (finProdFinEquiv.symm a).1) *
        Psi B (finProdFinEquiv.symm a).2
    rw [hPhi, hPsi]

@[simp]
theorem rankOneFlattened_apply
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ))
    (A : Configuration d G) (a : Fin (m * n)) :
    rankOneFlattened Phi Psi A a =
      star (Phi A (finProdFinEquiv.symm a).1) *
        Psi A (finProdFinEquiv.symm a).2 :=
  rfl

@[simp]
theorem rankOneFlattened_support
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ)) :
    (rankOneFlattened Phi Psi).support = Phi.support ∪ Psi.support :=
  rfl

/-- The Hilbert--Schmidt norm of the flattened rank-one matrix is exactly the
product of the Euclidean endpoint norms. -/
theorem endpointL2Norm_rankOneFlattened
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ))
    (A : Configuration d G) :
    endpointL2Norm (rankOneFlattened Phi Psi A) =
      endpointL2Norm (Phi A) * endpointL2Norm (Psi A) := by
  change ‖WithLp.toLp 2 (rankOneFlattened Phi Psi A)‖ =
    ‖WithLp.toLp 2 (Phi A)‖ * ‖WithLp.toLp 2 (Psi A)‖
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [← (finProdFinEquiv (m := m) (n := n)).sum_comp]
  simp only [rankOneFlattened_apply, Equiv.symm_apply_apply, norm_mul,
    norm_star, mul_pow]
  rw [Fintype.sum_prod_type]
  exact (Fintype.sum_mul_sum
    (fun i : Fin m => ‖Phi A i‖ ^ 2)
    (fun j : Fin n => ‖Psi A j‖ ^ 2)).symm

/-- Two pointwise normalized endpoint fields produce a pointwise normalized
rank-one Hilbert--Schmidt field. -/
theorem endpointL2Norm_rankOneFlattened_le_one
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ))
    (hPhi : ∀ A, endpointL2Norm (Phi A) ≤ 1)
    (hPsi : ∀ A, endpointL2Norm (Psi A) ≤ 1)
    (A : Configuration d G) :
    endpointL2Norm (rankOneFlattened Phi Psi A) ≤ 1 := by
  rw [endpointL2Norm_rankOneFlattened]
  calc
    endpointL2Norm (Phi A) * endpointL2Norm (Psi A) ≤ 1 * 1 :=
      mul_le_mul (hPhi A) (hPsi A) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Anti-diagonal positive-half support is preserved when the two endpoint
collars are assembled into their flattened rank-one matrix. -/
theorem rankOneFlattened_supportedInAntiDiagonalPositiveHalf
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ))
    (τ σ : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPsi : Psi.SupportedInAntiDiagonalPositiveHalf τ σ k) :
    (rankOneFlattened Phi Psi).SupportedInAntiDiagonalPositiveHalf τ σ k := by
  exact EdgeSet.antiDiagonal_union hPhi hPsi

/-- Every matrix coordinate belongs to the scalar anti-diagonal positive
algebra whenever both endpoint collars do. -/
theorem rankOneFlattened_component_supportedInAntiDiagonalPositiveHalf
    (Phi : LocalField d G (Fin m → ℂ))
    (Psi : LocalField d G (Fin n → ℂ))
    (τ σ : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPsi : Psi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (a : Fin (m * n)) :
    ((rankOneFlattened Phi Psi).component a).SupportedInAntiDiagonalPositiveHalf
      τ σ k := by
  exact rankOneFlattened_supportedInAntiDiagonalPositiveHalf
    Phi Psi τ σ k hPhi hPsi

end

end YangMills.Gluelump.Endpoint
