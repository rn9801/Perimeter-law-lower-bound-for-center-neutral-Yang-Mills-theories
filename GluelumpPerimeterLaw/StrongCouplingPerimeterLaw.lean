/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw

/-!
# Strong-coupling specialization of the center-neutral perimeter law

This module is a one-way application adapter.  It specializes the abstract
completed-free-boundary theorem to the cluster-constructed centered
infinite-volume Wilson probability.  The neutral reflection-propagation
chain does not import this module.
-/

namespace YangMills.Gluelump.InfiniteVolume

open MeasureTheory YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.StrongCoupling
open YangMills.Gluelump.RepresentationTheory
open Representation

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

/-- The cluster-constructed centered Wilson state obeys the center-neutral
perimeter lower bound throughout the positive strong-coupling interval.

The rate is chosen before the strong-coupling-radius witness and before all
rectangle data.  Thus it has exactly the dependencies of the abstract
theorem: `d`, `sigma`, `rho`, and `beta`. -/
theorem centeredInfiniteVolume_centerNeutralPerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (hd : 3 ≤ d)
    (hsigma : Function.Injective sigma.ρ)
    (hirreducible : (asRepresentation rho).IsIrreducible)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbetaPos : 0 < beta) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ hbeta : ‖(beta : ℂ)‖ <
          latticeStrongCouplingRadius d sigma.wilsonPotential.bound,
        ∀ (x₀ : Site d) (a b : Fin d) (R T : ℕ),
          a ≠ b → 0 < R → 0 < T →
            complexRectangleWilsonExpectation
                (centeredInfiniteVolumeProbability
                  (fun _ ↦ (1 : Configuration d G))
                  sigma.wilsonPotential beta hbeta)
                rho x₀ a b R T =
                (rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T : ℂ) ∧
              Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T := by
  obtain ⟨rate, hrate, hbound⟩ :=
    centerNeutralInfiniteVolumePerimeterLaw sigma rho
      hd hsigma hirreducible hcenter beta hbetaPos
  refine ⟨rate, hrate, ?_⟩
  intro hbeta x₀ a b R T hab hR hT
  exact hbound
    (centeredInfiniteVolumeProbability
      (fun _ ↦ (1 : Configuration d G))
      sigma.wilsonPotential beta hbeta)
    (wilsonStrongCoupling_isTranslationInvariantFreeBoundaryLimit
      sigma beta hbeta)
    x₀ a b R T hab hR hT

end

end YangMills.Gluelump.InfiniteVolume
