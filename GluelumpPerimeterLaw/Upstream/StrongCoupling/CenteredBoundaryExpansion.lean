/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.CenteredBoundaryExpansion

/-! Additive uniform-coupling boundary estimate used by this package. -/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

local instance gluelumpCenteredBoundaryDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The cutoff in the centered boundary estimate is purely geometric and can
therefore be chosen simultaneously for every coupling in the strong-coupling
disk. -/
theorem norm_centered_complexGibbsExpectation_boundary_sub_le_eventually_uniform_beta
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (r : ℕ) :
    ∃ N, ∀ β : ℂ,
      ‖β‖ < latticeStrongCouplingRadius d Φ.bound →
      ∀ n, N ≤ n → ∀ η η' : Configuration d G,
        ‖complexGibbsExpectation F (centeredSpecification n η) Φ β -
          complexGibbsExpectation F (centeredSpecification n η') Φ β‖ ≤
        2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β *
          plaquetteClusterDecayRate (d := d) Φ β ^ r := by
  obtain ⟨N, hN⟩ := centered_boundaryDisagreement_distance_eventually F r
  refine ⟨N, fun β hβ n hn η η' => ?_⟩
  obtain ⟨hF, hdist⟩ := hN n hn η η'
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β
  let x := ‖complexGibbsExpectation F (centeredSpecification n η) Φ β -
    complexGibbsExpectation F (centeredSpecification n η') Φ β‖
  have ht : 0 < t := zero_lt_one.trans (one_lt_plaquetteCardinalityTilt Φ hβ)
  have htx : t ^ r * x ≤ B := by
    simpa [t, B, x, centeredSpecification, withExterior] using
      (pow_mul_norm_complexGibbsExpectation_withExterior_sub_le_boundaryBudget
        F (centeredSpecification n η) Φ hβ η η' hF r hdist)
  calc
    x = (t ^ r)⁻¹ * (t ^ r * x) := by field_simp
    _ ≤ (t ^ r)⁻¹ * B :=
      mul_le_mul_of_nonneg_left htx (inv_nonneg.mpr (pow_nonneg ht.le r))
    _ = B * (t⁻¹) ^ r := by
      rw [inv_pow]
      ring
    _ = _ := by rfl

end

end YangMills.StrongCoupling
