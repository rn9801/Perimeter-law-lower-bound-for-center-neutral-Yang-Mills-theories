/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.CenteredGibbsTower

/-! Additive uniform-coupling cross-volume estimate used by this package. -/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open YangMills.Probability

noncomputable section

local instance gluelumpCenteredTowerDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The common cutoff in the cross-volume comparison is independent of the
coupling. Only the explicit right-hand side varies with `β`. -/
theorem norm_centered_complexGibbsExpectation_crossVolume_le_eventually_uniform_beta
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (r : ℕ) :
    ∃ N, ∀ β : ℝ,
      ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound →
      ∀ m n, N ≤ m → N ≤ n →
        ∀ ηm ηn : Configuration d G,
        ‖complexGibbsExpectation F (centeredSpecification m ηm) Φ (β : ℂ) -
          complexGibbsExpectation F (centeredSpecification n ηn) Φ (β : ℂ)‖ ≤
        2 * observableCardinalityTiltDecorationBudget (d := d) F Φ (β : ℂ) *
          plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually_uniform_beta
      F Φ r
  refine ⟨N, fun β hβ m n hm hn ηm ηn => ?_⟩
  by_cases hmn : m ≤ n
  · rw [norm_sub_rev]
    exact norm_complexGibbsExpectation_large_sub_centered_le_of_uniform
      hmn ηn ηm F Φ β _ (fun ξ => hN (β : ℂ) hβ m hm ξ ηm)
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    exact norm_complexGibbsExpectation_large_sub_centered_le_of_uniform
      hnm ηm ηn F Φ β _ (fun ξ => hN (β : ℂ) hβ n hn ξ ηn)

end

end YangMills.StrongCoupling
