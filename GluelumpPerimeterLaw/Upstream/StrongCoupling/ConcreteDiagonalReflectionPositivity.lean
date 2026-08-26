/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflectionBridge
import GluelumpPerimeterLaw.Upstream.StrongCoupling.InfiniteVolumeDiagonalReflectionPositivity
import YangMills.StrongCoupling.ConcreteDiagonalReflectionPositivity

/-!
# Downstream concrete diagonal reflection extensions

This file contains additive declarations needed by the gluelump development
that are not yet available on the pinned upstream `main` branch.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Finite centered identity-exterior Wilson laws have a Hermitian diagonal
reflection pairing. -/
theorem centeredGibbsSequence_one_diagonalReflectionHermitian
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (m : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ) :
    DiagonalReflectionHermitian
      (centeredGibbsSequence (fun _ ↦ (1 : Configuration d G))
        ρ.wilsonPotential β m : Measure (Configuration d G)) τ σ 0 := by
  intro _ F H hF hH
  let Λ := centeredSpecification m (1 : Configuration d G)
  have hfinite := Λ.integral_gibbsMeasure_diagonalReflectionProduct_conj_symm
    τ σ 0 (centeredSpecification_one_diagonalSymmetric m hτσ)
    ρ β F H hF hH
  unfold diagonalReflectionPairing
  simp only [centeredGibbsSequence]
  change star (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (H.diagonalReflectionProduct τ σ 0 F)) =
    localExpectation (fullGibbsProbability Λ ρ.wilsonPotential β)
      (F.diagonalReflectionProduct τ σ 0 H)
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Every finite centered identity-exterior Wilson law is invariant under a
coordinate-diagonal reflection through the origin. -/
theorem centeredGibbsSequence_one_integral_diagonalReflectionPullback
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (m : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (F : LocalObservable d G) :
    localExpectation
        (centeredGibbsSequence (fun _ ↦ (1 : Configuration d G))
          ρ.wilsonPotential β m)
        (F.diagonalReflectionPullback τ σ 0) =
      localExpectation
        (centeredGibbsSequence (fun _ ↦ (1 : Configuration d G))
          ρ.wilsonPotential β m) F := by
  let Λ := centeredSpecification m (1 : Configuration d G)
  simp only [centeredGibbsSequence, localExpectation_fullGibbsProbability]
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  simp only [LocalObservable.diagonalReflectionPullback_apply]
  change (∫ V, F (diagonalReflectConfiguration τ σ 0 (Λ.evaluate V))
      ∂Gauge.FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
    ∫ V, F (Λ.evaluate V)
      ∂Gauge.FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β
  exact Λ.integral_gibbsMeasure_diagonalReflectConfiguration τ σ 0
    (centeredSpecification_one_diagonalSymmetric m hτσ) ρ β F

/-- The strong-coupling infinite-volume Wilson state is invariant under
coordinate-diagonal reflection through the origin. -/
theorem centeredInfiniteVolume_integral_diagonalReflectionPullback
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (F : LocalObservable d G) :
    ∫ A, F (diagonalReflectConfiguration τ σ 0 A)
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ =
      ∫ A, F A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ := by
  let oneExterior : ℕ → Configuration d G := fun _ ↦ 1
  have hleft := tendsto_centered_localExpectation_infiniteVolume
    oneExterior ρ.wilsonPotential β hβ
      (F.diagonalReflectionPullback τ σ 0)
  have hright := tendsto_centered_localExpectation_infiniteVolume
    oneExterior ρ.wilsonPotential β hβ F
  have heq : (fun m ↦ localExpectation
      (centeredGibbsSequence oneExterior ρ.wilsonPotential β m)
        (F.diagonalReflectionPullback τ σ 0)) =
      fun m ↦ localExpectation
        (centeredGibbsSequence oneExterior ρ.wilsonPotential β m) F := by
    funext m
    exact centeredGibbsSequence_one_integral_diagonalReflectionPullback
      ρ β m hτσ F
  rw [heq] at hleft
  have hlimits := tendsto_nhds_unique hleft hright
  have hlimits' :
      (∫ A, F (diagonalReflectConfiguration τ σ 0 A)
          ∂centeredInfiniteVolumeMeasure oneExterior
            ρ.wilsonPotential β hβ) =
        ∫ A, F A ∂centeredInfiniteVolumeMeasure oneExterior
          ρ.wilsonPotential β hβ := by
    simpa only [LocalObservable.diagonalReflectionPullback_apply] using hlimits
  have hboundary := centeredInfiniteVolumeMeasure_boundary_independent
    oneExterior η ρ.wilsonPotential β hβ
  calc
    (∫ A, F (diagonalReflectConfiguration τ σ 0 A)
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) =
        ∫ A, F A ∂centeredInfiniteVolumeMeasure oneExterior
          ρ.wilsonPotential β hβ := by
      rw [← hboundary]
      exact hlimits'
    _ = ∫ A, F A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ := by
      rw [hboundary]

/-- Concrete infinite-volume diagonal pairing is Hermitian on every affine
parallel plane. -/
theorem centeredInfiniteVolume_diagonalReflectionHermitian
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  let oneExterior : ℕ → Configuration d G := fun _ ↦ 1
  have hzeroOne : DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure oneExterior ρ.wilsonPotential β hβ)
        τ σ 0 := by
    apply centeredInfiniteVolume_diagonalReflectionHermitian_of_eventually
    exact Filter.Eventually.of_forall fun m ↦
      centeredGibbsSequence_one_diagonalReflectionHermitian ρ β m hτσ
  have hzero :=
    centeredInfiniteVolume_diagonalReflectionHermitian_boundary_independent
      oneExterior η ρ.wilsonPotential β hβ τ σ 0 hzeroOne
  exact centeredInfiniteVolume_diagonalReflectionHermitian_all_planes
    η ρ.wilsonPotential β hβ hτσ hzero k

end

end YangMills.StrongCoupling
