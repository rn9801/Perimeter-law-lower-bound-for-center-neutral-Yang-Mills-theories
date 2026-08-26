/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.AntiDiagonalReflection
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteDiagonalReflectionPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteSiteReflectionPositivity

/-!
# Anti-diagonal reflection positivity for the strong-coupling state

The anti-diagonal plane `x τ + x σ = k` is conjugate to the diagonal plane
`x τ - x σ = k` by the coordinate flip `x σ ↦ -x σ`.  Coordinate-flip
invariance of the centered infinite-volume Yang--Mills measure therefore
transports diagonal reflection positivity, Hermitian symmetry, and
Cauchy--Schwarz without a second finite-volume reflection argument.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Reflection positivity through `x τ + x σ = k`. -/
def AntiDiagonalReflectionPositive
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    Complex.im (∫ A, F.antiDiagonalReflectionProduct τ σ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A,
        F.antiDiagonalReflectionProduct τ σ k F A ∂μ)

/-- Pairing associated with reflection through `x τ + x σ = k`. -/
def antiDiagonalReflectionPairing
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.antiDiagonalReflectionProduct τ σ k H A ∂μ

/-- Cauchy--Schwarz for the anti-diagonal reflection pairing. -/
def AntiDiagonalReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    H.SupportedInAntiDiagonalPositiveHalf τ σ k →
    Complex.normSq (antiDiagonalReflectionPairing μ τ σ k F H) ≤
      Complex.re (antiDiagonalReflectionPairing μ τ σ k F F) *
        Complex.re (antiDiagonalReflectionPairing μ τ σ k H H)

/-- Hermitian symmetry of the anti-diagonal reflection pairing. -/
def AntiDiagonalReflectionHermitian
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    H.SupportedInAntiDiagonalPositiveHalf τ σ k →
    star (antiDiagonalReflectionPairing μ τ σ k H F) =
      antiDiagonalReflectionPairing μ τ σ k F H

/-- Coordinate-flip invariance identifies the anti-diagonal pairing with the
ordinary diagonal pairing of the pulled-back observables. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ) (F H : LocalObservable d G) :
    antiDiagonalReflectionPairing
        (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k F H =
      diagonalReflectionPairing
        (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k
        (F.siteReflectionPullback σ 0)
        (H.siteReflectionPullback σ 0) := by
  let O := F.antiDiagonalReflectionProduct τ σ k H
  have hinv := centeredInfiniteVolume_integral_siteReflectionPullback
    η Φ β hβ σ O
  unfold antiDiagonalReflectionPairing diagonalReflectionPairing
  calc
    (∫ A, O A ∂centeredInfiniteVolumeMeasure η Φ β hβ) =
        ∫ A, O (siteReflectConfiguration σ 0 A)
          ∂centeredInfiniteVolumeMeasure η Φ β hβ := hinv.symm
    _ = ∫ A,
        (F.siteReflectionPullback σ 0).diagonalReflectionProduct τ σ k
          (H.siteReflectionPullback σ 0) A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
      apply integral_congr_ae
      filter_upwards with A
      simpa only [LocalObservable.siteReflectionPullback_apply] using
        F.antiDiagonalReflectionProduct_siteReflectionPullback_apply
          τ σ k H A

/-- Anti-diagonal reflection positivity follows by conjugation from diagonal
reflection positivity. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionPositive
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    AntiDiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  intro _ F hF
  have hD := centeredInfiniteVolume_diagonalReflectionPositive
    η ρ β hβ0 hβ hτσ k
  have hsupport := hF.siteReflectionPullback hτσ
  have hpos := hD hτσ (F.siteReflectionPullback σ 0) hsupport
  change Complex.im (antiDiagonalReflectionPairing
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ)
        τ σ k F F) = 0 ∧
    0 ≤ Complex.re (antiDiagonalReflectionPairing
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ)
        τ σ k F F)
  rw [centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
    η ρ.wilsonPotential β hβ τ σ k F F]
  exact hpos

/-- Anti-diagonal Cauchy--Schwarz, obtained with no new reflection-positivity
normal form. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionCauchySchwarz
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    AntiDiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  intro _ F H hF hH
  have hD := centeredInfiniteVolume_diagonalReflectionCauchySchwarz
    η ρ β hβ0 hβ hτσ k
  have hCS := hD hτσ
    (F.siteReflectionPullback σ 0) (H.siteReflectionPullback σ 0)
    (hF.siteReflectionPullback hτσ) (hH.siteReflectionPullback hτσ)
  rw [centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
      η ρ.wilsonPotential β hβ τ σ k F H,
    centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
      η ρ.wilsonPotential β hβ τ σ k F F,
    centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
      η ρ.wilsonPotential β hβ τ σ k H H]
  exact hCS

/-- Anti-diagonal Hermitian symmetry, also transported by conjugation. -/
theorem centeredInfiniteVolume_antiDiagonalReflectionHermitian
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    AntiDiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  intro _ F H hF hH
  have hD := centeredInfiniteVolume_diagonalReflectionHermitian
    η ρ β hβ hτσ k
  have hherm := hD hτσ
    (F.siteReflectionPullback σ 0) (H.siteReflectionPullback σ 0)
    (hF.siteReflectionPullback hτσ) (hH.siteReflectionPullback hτσ)
  rw [centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
      η ρ.wilsonPotential β hβ τ σ k H F,
    centeredInfiniteVolume_antiDiagonalReflectionPairing_eq_diagonal
      η ρ.wilsonPotential β hβ τ σ k F H]
  exact hherm

end

end YangMills.StrongCoupling
