/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionBridge
import GluelumpPerimeterLaw.Upstream.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.ConcreteLinkReflectionPositivity

/-! Additive uniform-coupling link-box comparison used by this package. -/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

local instance gluelumpConcreteLinkDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The link-symmetric-to-centered comparison has one geometric cutoff valid
simultaneously for all real couplings in the strong-coupling interval. -/
theorem norm_linkSymmetric_sub_centered_le_eventually_uniform_beta
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G)
    (τ : Fin d) (r : ℕ) :
    ∃ N, ∀ β : ℝ,
      ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound →
      ∀ n, N ≤ n → ∀ η : Configuration d G,
        ‖complexGibbsExpectation F (linkSymmetricSpecification G d n τ)
            Φ (β : ℂ) -
          complexGibbsExpectation F (centeredSpecification n η) Φ (β : ℂ)‖ ≤
        2 * observableCardinalityTiltDecorationBudget (d := d) F Φ (β : ℂ) *
          plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually_uniform_beta
      F Φ r
  refine ⟨N, fun β hβ n hn η => ?_⟩
  let small := centeredSpecification n η
  let large := linkSymmetricSpecification G d n τ
  let h : FiniteSubspecification small large :=
    centeredToLinkSymmetricSubspecification n τ η
  apply h.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    η F Φ β _
  intro ξ
  simpa only [small, centeredSpecification] using hN (β : ℂ) hβ n hn ξ η

end

end YangMills.StrongCoupling
