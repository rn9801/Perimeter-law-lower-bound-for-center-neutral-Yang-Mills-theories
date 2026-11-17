/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteGaugeFixedFactorization
import GluelumpPerimeterLaw.OneLink.ConjugationSpanBoundaryMode
import GluelumpPerimeterLaw.OneLink.LocalIncidence

/-!
# Concrete finite energy for a split link-reflection side

Changing the selected endpoint coordinates while holding the remote
coordinates fixed changes the positive half-box weight by a factor depending
only on the corresponding physical edge collar.  This file discharges the
pointwise comparison hypothesis used by the abstract endpoint-mass and
remote-kernel estimates.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson

noncomputable section

universe u

variable {d n : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Pairwise finite-energy comparison for an arbitrary selected side collar
identified with a fixed finite set of physical stored edges. -/
theorem splitPositiveBoltzmannWeight_pair_compare
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (sigma : ContinuousUnitaryRepData G n)
    (selected : Lambda.linkPositiveEdges tau k → Prop)
    [DecidablePred selected]
    (E : Finset (PositiveEdge d))
    (hselected : ∀ p, selected p ↔ p.1 ∈ E)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (u u' : CollarCoordinate selected → G)
    (r : RemoteCoordinate selected → G) :
    let c := collarFiniteEnergyFactor beta sigma.wilsonPotential E
    let F := splitPositiveBoltzmannWeight
      (Lambda.linkWilsonDecomposition tau k hLambda sigma) selected beta
    c * F (u', r) ≤ F (u, r) ∧ c * F (u, r) ≤ F (u', r) := by
  let D := Lambda.linkWilsonDecomposition tau k hLambda sigma
  let merge := (splitSideMeasurableEquiv (G := G) selected).symm
  let U := merge (u, r)
  let V := merge (u', r)
  have hUV : ∀ p, p.1 ∉ E → U p = V p := by
    intro p hp
    exact mergeSide_apply_of_not_selected selected u u' r p
      (fun hs ↦ hp ((hselected p).mp hs))
  have hVU : ∀ p, p.1 ∉ E → V p = U p := by
    intro p hp
    exact (hUV p hp).symm
  constructor
  · simpa only [splitPositiveBoltzmannWeight_apply, D, U, V, merge] using
      collarFiniteEnergyFactor_mul_exp_linkPositiveAction_le
        Lambda tau k hLambda hbeta sigma E U V hUV
  · simpa only [splitPositiveBoltzmannWeight_apply, D, U, V, merge] using
      collarFiniteEnergyFactor_mul_exp_linkPositiveAction_le
        Lambda tau k hLambda hbeta sigma E V U hVU

/-- The preceding comparison specialized to the physical comb collar used
by the direct conjugation-span endpoint.  Its finite-energy constant is
manifestly independent of the ambient box. -/
theorem linkComb_splitPositiveBoltzmannWeight_pair_compare
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    {m : ℕ} (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (u u' : CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x) → G)
    (r : RemoteCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x) → G) :
    let E := combEndpointCollar (m := m) hd x
    let c := collarFiniteEnergyFactor beta sigma.wilsonPotential E
    let F := splitPositiveBoltzmannWeight
      (Lambda.linkWilsonDecomposition tau k hLambda sigma)
      (linkCombSelected (m := m) Lambda tau k hd x) beta
    c * F (u', r) ≤ F (u, r) ∧ c * F (u, r) ≤ F (u', r) := by
  exact splitPositiveBoltzmannWeight_pair_compare
    Lambda tau k hLambda sigma
    (linkCombSelected (m := m) Lambda tau k hd x)
    (combEndpointCollar (m := m) hd x) (fun _p ↦ Iff.rfl)
    hbeta u u' r

end

end YangMills.Gluelump.OneLink
