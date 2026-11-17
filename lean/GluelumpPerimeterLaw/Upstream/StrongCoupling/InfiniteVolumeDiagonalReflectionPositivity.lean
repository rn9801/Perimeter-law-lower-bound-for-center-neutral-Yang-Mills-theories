/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflectionPositivity
import YangMills.StrongCoupling.InfiniteVolumeDiagonalReflectionPositivity

/-!
# Downstream extensions for infinite-volume diagonal reflection positivity

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

/-- Hermitian symmetry of the diagonal reflection pairing on the positive
local algebra. -/
def DiagonalReflectionHermitian
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    H.SupportedInDiagonalPositiveHalf τ σ k →
    star (diagonalReflectionPairing μ τ σ k H F) =
      diagonalReflectionPairing μ τ σ k F H

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Hermitian symmetry is preserved by convergence of all local
expectations. -/
theorem diagonalReflectionHermitian_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n ↦ localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionHermitian (μn n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionHermitian μ τ σ k := by
  intro hτσ F H hF hH
  let OHF := H.diagonalReflectionProduct τ σ k F
  let OFH := F.diagonalReflectionProduct τ σ k H
  have hleft : Tendsto
      (fun n ↦ star (localExpectation (μn n) OHF)) atTop
      (nhds (star (∫ A, OHF A ∂μ))) :=
    continuous_star.continuousAt.tendsto.comp (hlim OHF)
  have hright := hlim OFH
  have heq : (fun n ↦ star (localExpectation (μn n) OHF)) =ᶠ[atTop]
      fun n ↦ localExpectation (μn n) OFH := by
    filter_upwards [hfinite] with n hn
    exact hn hτσ F H hF hH
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

/-- Cluster-expansion passage of diagonal Hermitian symmetry to the
constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_diagonalReflectionHermitian_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionHermitian
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  exact diagonalReflectionHermitian_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Diagonal Hermitian symmetry is independent of the exterior sequence. -/
theorem centeredInfiniteVolume_diagonalReflectionHermitian_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (h : DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k) :
    DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ σ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Translation invariance transfers Hermitian symmetry of the diagonal
pairing from `x τ = x σ` to every affine parallel plane. -/
theorem centeredInfiniteVolume_diagonalReflectionHermitian_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ 0) :
    ∀ k : ℤ, DiagonalReflectionHermitian
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  intro k _ F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInDiagonalPositiveHalf τ σ k) :
      (K.translatePullback v).SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hFt := translateSupport F hF
  have hHt := translateSupport H hH
  have hHerm := hzero hτσ Ft Ht hFt hHt
  have pairing_translate (K L : LocalObservable d G) :
      diagonalReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k K L =
        diagonalReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ 0
            (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := centeredInfiniteVolume_integral_translatePullback
      η Φ β hβ v (K.diagonalReflectionProduct τ σ k L)
    rw [diagonalReflectionPairing, diagonalReflectionPairing, ← htranslate]
    apply integral_congr_ae
    apply ae_of_all
    intro A
    change star (K (diagonalReflectConfiguration τ σ k
        (LocalObservable.translateConfiguration v A))) *
          L (LocalObservable.translateConfiguration v A) =
      star (K (LocalObservable.translateConfiguration v
        (diagonalReflectConfiguration τ σ 0 A))) *
          L (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  rw [pairing_translate H F, pairing_translate F H]
  exact hHerm

end

end YangMills.StrongCoupling
