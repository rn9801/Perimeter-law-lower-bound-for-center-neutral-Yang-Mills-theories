/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.RankOne
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteAntiDiagonalReflectionPositivity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite-family anti-diagonal reflection Cauchy--Schwarz

This is the direct-sum reflection space used by the matrix-valued second
corner step.  A matrix is represented by any finite coordinate family; in
particular its two indices may be flattened into `Fin m` before applying the
endpoint comparison theorem.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson StrongCoupling

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G]

/-- Direct sum of scalar anti-diagonal reflection pairings. -/
def antiDiagonalReflectionFamilyPairing {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (F H : ι → LocalObservable d G) : ℂ :=
  ∑ i, antiDiagonalReflectionPairing μ τ σ k (F i) (H i)

/-- Scalar anti-diagonal positivity and Cauchy--Schwarz imply the finite
direct-sum inequality used for matrix coordinates. -/
theorem antiDiagonalReflectionFamilyCauchySchwarz
    {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration d G)) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ)
    (hpos : AntiDiagonalReflectionPositive μ τ σ k)
    (hcs : AntiDiagonalReflectionCauchySchwarz μ τ σ k)
    (F H : ι → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hH : ∀ i, (H i).SupportedInAntiDiagonalPositiveHalf τ σ k) :
    Complex.normSq (antiDiagonalReflectionFamilyPairing μ τ σ k F H) ≤
      (∑ i, Complex.re
        (antiDiagonalReflectionPairing μ τ σ k (F i) (F i))) *
      ∑ i, Complex.re
        (antiDiagonalReflectionPairing μ τ σ k (H i) (H i)) := by
  let p : ι → ℂ := fun i =>
    antiDiagonalReflectionPairing μ τ σ k (F i) (H i)
  let a : ι → ℝ := fun i => Complex.re
    (antiDiagonalReflectionPairing μ τ σ k (F i) (F i))
  let b : ι → ℝ := fun i => Complex.re
    (antiDiagonalReflectionPairing μ τ σ k (H i) (H i))
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := by
    intro i _hi
    exact (hpos hτσ (F i) (hF i)).2
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := by
    intro i _hi
    exact (hpos hτσ (H i) (hH i)).2
  have hp : ∀ i ∈ Finset.univ, ‖p i‖ ^ 2 ≤ a i * b i := by
    intro i _hi
    rw [Complex.sq_norm]
    exact hcs hτσ (F i) (H i) (hF i) (hH i)
  have hsumNorm : ‖∑ i, p i‖ ≤ ∑ i, ‖p i‖ :=
    norm_sum_le Finset.univ p
  calc
    Complex.normSq (antiDiagonalReflectionFamilyPairing μ τ σ k F H) =
        ‖∑ i, p i‖ ^ 2 := by
      rw [Complex.sq_norm]
      rfl
    _ ≤ (∑ i, ‖p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsumNorm 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ha hb hp
    _ = (∑ i, Complex.re
          (antiDiagonalReflectionPairing μ τ σ k (F i) (F i))) *
        ∑ i, Complex.re
          (antiDiagonalReflectionPairing μ τ σ k (H i) (H i)) := rfl

/-- Direct-sum Cauchy--Schwarz loses no factor when the comparison family's
reflection norm is at most one. -/
theorem antiDiagonalReflectionFamily_normSq_le_left_of_right_le_one
    {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration d G)) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ)
    (hpos : AntiDiagonalReflectionPositive μ τ σ k)
    (hcs : AntiDiagonalReflectionCauchySchwarz μ τ σ k)
    (F H : ι → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hH : ∀ i, (H i).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hHone : (∑ i, Complex.re
      (antiDiagonalReflectionPairing μ τ σ k (H i) (H i))) ≤ 1) :
    Complex.normSq (antiDiagonalReflectionFamilyPairing μ τ σ k F H) ≤
      ∑ i, Complex.re
        (antiDiagonalReflectionPairing μ τ σ k (F i) (F i)) := by
  have hfamily := antiDiagonalReflectionFamilyCauchySchwarz
    μ hτσ k hpos hcs F H hF hH
  have hleft : 0 ≤ ∑ i, Complex.re
      (antiDiagonalReflectionPairing μ τ σ k (F i) (F i)) :=
    Finset.sum_nonneg fun i _ => (hpos hτσ (F i) (hF i)).2
  exact hfamily.trans <| by
    simpa using mul_le_of_le_one_right hleft hHone

variable [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

omit [T2Space G] [GaugeHaarProbability G] in
/-- A normalized finite-dimensional comparison field has anti-diagonal
reflection norm at most one.  This applies directly to the flattened
rank-one endpoint matrix once its pointwise Hilbert--Schmidt norm bound has
been established. -/
theorem endpointComponentFamily_antiDiagonalSelfPairing_re_le_one
    (μ : ProbabilityMeasure (Configuration d G))
    (Phi : Endpoint.LocalField d G (Fin n → ℂ))
    (hPhi : ∀ A, Endpoint.endpointL2Norm (Phi A) ≤ 1)
    (τ σ : Fin d) (k : ℤ) :
    Complex.re (antiDiagonalReflectionFamilyPairing
      (μ : Measure (Configuration d G)) τ σ k
      (fun i => Phi.component i) (fun i => Phi.component i)) ≤ 1 := by
  have hintegrable : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun A =>
        (Phi.component i).antiDiagonalReflectionProduct τ σ k
          (Phi.component i) A) (μ : Measure (Configuration d G)) := by
    intro i _hi
    exact integrable_localObservable μ
      ((Phi.component i).antiDiagonalReflectionProduct τ σ k
        (Phi.component i))
  have hpairing :
      antiDiagonalReflectionFamilyPairing (μ : Measure (Configuration d G))
          τ σ k (fun i => Phi.component i) (fun i => Phi.component i) =
        ∫ A, Endpoint.hermitianPairing
          (Phi (antiDiagonalReflectConfiguration τ σ k A)) (Phi A) ∂μ := by
    unfold antiDiagonalReflectionFamilyPairing antiDiagonalReflectionPairing
    rw [← integral_finsetSum Finset.univ hintegrable]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      simp only [LocalObservable.antiDiagonalReflectionProduct_apply,
        Endpoint.LocalField.component_apply, Endpoint.hermitianPairing]
  rw [hpairing]
  calc
    Complex.re (∫ A, Endpoint.hermitianPairing
        (Phi (antiDiagonalReflectConfiguration τ σ k A)) (Phi A) ∂μ) ≤
        ‖∫ A, Endpoint.hermitianPairing
          (Phi (antiDiagonalReflectConfiguration τ σ k A)) (Phi A) ∂μ‖ :=
      Complex.re_le_norm _
    _ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (μ : Measure (Configuration d G))) (C := (1 : ℝ)) <|
          ae_of_all _ fun A => by
            calc
              ‖Endpoint.hermitianPairing
                  (Phi (antiDiagonalReflectConfiguration τ σ k A)) (Phi A)‖ ≤
                  Endpoint.endpointL2Norm
                      (Phi (antiDiagonalReflectConfiguration τ σ k A)) *
                    Endpoint.endpointL2Norm (Phi A) :=
                Endpoint.norm_hermitianPairing_le _ _
              _ ≤ 1 * 1 := mul_le_mul
                (hPhi (antiDiagonalReflectConfiguration τ σ k A)) (hPhi A)
                (by exact norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1

/-- Concrete paper-style anti-diagonal Cauchy--Schwarz against a normalized
finite coordinate family. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionFamily_endpointComparison
    (eta : ℕ → Configuration d G)
    {nρ : ℕ} (rho : ContinuousUnitaryRepData G nρ)
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (F : Fin n → LocalObservable d G)
    (Phi : Endpoint.LocalField d G (Fin n → ℂ))
    (hF : ∀ i, (F i).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPhiSupport : ∀ i,
      (Phi.component i).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPhiNorm : ∀ A, Endpoint.endpointL2Norm (Phi A) ≤ 1) :
    Complex.normSq (antiDiagonalReflectionFamilyPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ σ k F (fun i => Phi.component i)) ≤
      ∑ i, Complex.re (antiDiagonalReflectionPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ σ k (F i) (F i)) := by
  apply antiDiagonalReflectionFamily_normSq_le_left_of_right_le_one
    (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
    hτσ k
    (centeredInfiniteVolume_antiDiagonalReflectionPositive
      eta rho beta hbeta0 hbeta hτσ k)
    (centeredInfiniteVolume_antiDiagonalReflectionCauchySchwarz
      eta rho beta hbeta0 hbeta hτσ k)
    F (fun i => Phi.component i) hF hPhiSupport
  simpa [centeredInfiniteVolumeMeasure,
    antiDiagonalReflectionFamilyPairing] using
    endpointComponentFamily_antiDiagonalSelfPairing_re_le_one
      (centeredInfiniteVolumeProbability eta rho.wilsonPotential beta hbeta)
      Phi hPhiNorm τ σ k

/-- The paper's comparison observable for the second corner: a flattened
rank-one endpoint matrix.  Both endpoint factors are retained, its support is
the union of their collars, and its reflection norm is bounded by one through
the exact Hilbert--Schmidt product formula. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionFamily_rankOneComparison
    (eta : ℕ → Configuration d G)
    {nρ : ℕ} (rho : ContinuousUnitaryRepData G nρ)
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    {m : ℕ}
    (F : Fin (m * n) → LocalObservable d G)
    (Phi : Endpoint.LocalField d G (Fin m → ℂ))
    (Psi : Endpoint.LocalField d G (Fin n → ℂ))
    (hF : ∀ a, (F a).SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPhiSupport : Phi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPsiSupport : Psi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPhiNorm : ∀ A, Endpoint.endpointL2Norm (Phi A) ≤ 1)
    (hPsiNorm : ∀ A, Endpoint.endpointL2Norm (Psi A) ≤ 1) :
    Complex.normSq (antiDiagonalReflectionFamilyPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ σ k F
        (fun a => (Endpoint.rankOneFlattened Phi Psi).component a)) ≤
      ∑ a, Complex.re (antiDiagonalReflectionPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ σ k (F a) (F a)) := by
  apply centeredInfiniteVolume_antiDiagonalReflectionFamily_endpointComparison
    eta rho beta hbeta0 hbeta hτσ k F
    (Endpoint.rankOneFlattened Phi Psi) hF
  · exact fun a =>
      Endpoint.rankOneFlattened_component_supportedInAntiDiagonalPositiveHalf
        Phi Psi τ σ k hPhiSupport hPsiSupport a
  · exact Endpoint.endpointL2Norm_rankOneFlattened_le_one
      Phi Psi hPhiNorm hPsiNorm

end

end YangMills.Gluelump.Propagation
