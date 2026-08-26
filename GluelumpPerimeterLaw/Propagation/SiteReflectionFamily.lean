/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ConcreteSiteReflectionPositivity
import YangMills.Wilson.Loop
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite-family site-reflection Cauchy--Schwarz

Wilson rectangles split at an integer coordinate plane into a finite family
of matrix coefficients.  This file lifts the repository's scalar
site-reflection form to the finite direct sum needed for that contraction.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson StrongCoupling

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G]

/-- Direct sum of scalar site-reflection pairings. -/
def siteReflectionFamilyPairing {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (F H : ι → LocalObservable d G) : ℂ :=
  ∑ i, siteReflectionPairing μ τ k (F i) (H i)

/-- Scalar site-reflection positivity and Cauchy--Schwarz imply Cauchy--Schwarz
on every finite direct sum. -/
theorem siteReflectionFamilyCauchySchwarz
    {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hpos : SiteReflectionPositive μ τ k)
    (hcs : SiteReflectionCauchySchwarz μ τ k)
    (F H : ι → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInSitePositiveHalf τ k)
    (hH : ∀ i, (H i).SupportedInSitePositiveHalf τ k) :
    Complex.normSq (siteReflectionFamilyPairing μ τ k F H) ≤
      (∑ i, Complex.re (siteReflectionPairing μ τ k (F i) (F i))) *
        ∑ i, Complex.re (siteReflectionPairing μ τ k (H i) (H i)) := by
  let p : ι → ℂ := fun i => siteReflectionPairing μ τ k (F i) (H i)
  let a : ι → ℝ := fun i =>
    Complex.re (siteReflectionPairing μ τ k (F i) (F i))
  let b : ι → ℝ := fun i =>
    Complex.re (siteReflectionPairing μ τ k (H i) (H i))
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := by
    intro i _hi
    exact (hpos (F i) (hF i)).2
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := by
    intro i _hi
    exact (hpos (H i) (hH i)).2
  have hp : ∀ i ∈ Finset.univ, ‖p i‖ ^ 2 ≤ a i * b i := by
    intro i _hi
    rw [Complex.sq_norm]
    exact hcs (F i) (H i) (hF i) (hH i)
  have hsumNorm : ‖∑ i, p i‖ ≤ ∑ i, ‖p i‖ :=
    norm_sum_le Finset.univ p
  calc
    Complex.normSq (siteReflectionFamilyPairing μ τ k F H) =
        ‖∑ i, p i‖ ^ 2 := by
      rw [Complex.sq_norm]
      rfl
    _ ≤ (∑ i, ‖p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsumNorm 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ha hb hp
    _ = (∑ i, Complex.re (siteReflectionPairing μ τ k (F i) (F i))) *
        ∑ i, Complex.re (siteReflectionPairing μ τ k (H i) (H i)) := rfl

variable [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Concrete infinite-volume site-reflection Cauchy--Schwarz for a finite
family of positive-half observables. -/
theorem centeredInfiniteVolume_siteReflectionFamilyCauchySchwarz
    {ι : Type*} [Fintype ι]
    (eta : ℕ → Configuration d G)
    {nρ : ℕ} (rho : ContinuousUnitaryRepData G nρ)
    (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ)
    (F H : ι → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInSitePositiveHalf τ k)
    (hH : ∀ i, (H i).SupportedInSitePositiveHalf τ k) :
    Complex.normSq (siteReflectionFamilyPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ k F H) ≤
      (∑ i, Complex.re (siteReflectionPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ k (F i) (F i))) *
      ∑ i, Complex.re (siteReflectionPairing
        (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
        τ k (H i) (H i)) := by
  exact siteReflectionFamilyCauchySchwarz
    (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
    τ k
    (centeredInfiniteVolume_siteReflectionPositive
      eta rho.wilsonPotential beta hbeta τ k)
    (centeredInfiniteVolume_siteReflectionCauchySchwarz
      eta rho.wilsonPotential beta hbeta τ k)
    F H hF hH

/-- Concrete infinite-volume positivity for a finite direct sum of
site-reflection pairings. -/
theorem centeredInfiniteVolume_siteReflectionFamilyPositive
    {ι : Type*} [Fintype ι]
    (eta : ℕ → Configuration d G)
    {nρ : ℕ} (rho : ContinuousUnitaryRepData G nρ)
    (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ)
    (F : ι → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInSitePositiveHalf τ k) :
    Complex.im (siteReflectionFamilyPairing
      (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
      τ k F F) = 0 ∧
    0 ≤ Complex.re (siteReflectionFamilyPairing
      (centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta)
      τ k F F) := by
  let μ := centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta
  have hpos := centeredInfiniteVolume_siteReflectionPositive
    eta rho.wilsonPotential beta hbeta τ k
  constructor
  · unfold siteReflectionFamilyPairing
    change Complex.imAddGroupHom (∑ i,
      siteReflectionPairing μ τ k (F i) (F i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => (hpos (F i) (hF i)).1
  · unfold siteReflectionFamilyPairing
    change 0 ≤ Complex.reAddGroupHom (∑ i,
      siteReflectionPairing μ τ k (F i) (F i))
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ => (hpos (F i) (hF i)).2

end

end YangMills.Gluelump.Propagation
