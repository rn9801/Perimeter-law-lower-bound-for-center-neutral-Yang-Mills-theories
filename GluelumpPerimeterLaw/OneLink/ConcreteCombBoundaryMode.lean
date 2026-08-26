/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.EndpointCombMode
import GluelumpPerimeterLaw.OneLink.CrossFeatureSplit

/-!
# The comb mode in concrete link-boundary coordinates

This file transports the fixed comb endpoint mode into the exact collar
coordinate type cut out of a finite link-reflection side, then embeds it into
the selected crossing-feature family.  The only box assumptions are that the
fixed collar fits and that each collar edge is represented by a crossing
plaquette; neither the degree nor the resulting coefficient cost depends on
the rest of the box.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson Endpoint RepresentationTheory
open Representation

noncomputable section

universe u

variable {d m r nsigma : ℕ} {G A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]

/-- Predicate selecting the fixed physical comb collar inside the strict
positive side-coordinate type. -/
def linkCombSelected
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    {m : ℕ} (hd : 3 ≤ d) (x : Site d)
    (p : Lambda.linkPositiveEdges tau k) : Prop :=
  p.1 ∈ combEndpointCollar (m := m) hd x

instance instDecidablePredLinkCombSelected
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    {m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    DecidablePred (linkCombSelected (m := m) Lambda tau k hd x) :=
  fun p ↦ Finset.decidableMem p.1 (combEndpointCollar (m := m) hd x)

/-- The physical comb collar and its selected side-coordinate realization
are canonically equivalent once the collar fits the specification. -/
def linkCombCollarEquiv
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    {m : ℕ} (hd : 3 ≤ d) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k) :
    combEndpointCollar (m := m) hd x ≃
      CollarCoordinate (linkCombSelected (m := m) Lambda tau k hd x) :=
  finsetEquivCollarCoordinate _ _ hcollar

/-- Endpoint coordinates on the selected side collar, obtained by exact
finite coordinate reindexing from the physical comb collar. -/
def linkCombPhiFamily
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A nsigma)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k) (i : Fin r) :
    C((CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x) → G), ℂ) :=
  (combPhiCollarCoordinate hd D adj rho T x i).comp
    ⟨fun U e ↦ U (linkCombCollarEquiv Lambda tau k hd x hcollar e), by
      apply continuous_pi
      intro e
      exact continuous_apply _⟩

/-- The concrete nonzero comb mode, rewritten in the selected side-collar
coordinates of an arbitrary fitting finite specification. -/
noncomputable def linkCombCollarMode
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A nsigma)
    (H : YangMills.Gluelump.Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k) :
    EndpointConjugateMode (matrixFeature D.sigma)
      (linkCombPhiFamily Lambda tau k hd D adj rho T x hcollar)
      (combEndpointDegree (m := m) hd x) := by
  simpa only [linkCombPhiFamily] using
    reindexMatrixEndpointMode D.sigma
      (linkCombCollarEquiv Lambda tau k hd x hcollar)
      (fun i ↦ combPhiCollarCoordinate hd D adj rho T x i)
      (combEndpointConjugateMode hd D H adj rho T hT x)

/-- The comb mode embedded in the exact selected crossing-feature family of
the concrete finite-volume link decomposition.  Repeated crossing labels are
kept in the target family; one visible label per collar edge suffices to
embed the mode. -/
noncomputable def linkCombEndpointCrossMode
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k) (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A nsigma)
    (H : YangMills.Gluelump.Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    EndpointConjugateMode
      ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau k hLambda hclosed D.sigma).endpointFeature
        (linkCombSelected (m := m) Lambda tau k hd x))
      (linkCombPhiFamily Lambda tau k hd D adj rho T x hcollar)
      (combEndpointDegree (m := m) hd x) := by
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed D.sigma
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let qOf : CollarCoordinate selected →
      {q : Lambda.linkCrossPlaquettes tau k // selected (data.edge q)} :=
    fun e ↦ by
      let physical : combEndpointCollar (m := m) hd x :=
        ⟨e.1.1, e.2⟩
      let q := Classical.choose (hvisible physical.1 physical.2)
      refine ⟨q, ?_⟩
      change FiniteSpecification.linkCrossPositiveEdge tau q.1 ∈
        combEndpointCollar (m := m) hd x
      rw [Classical.choose_spec (hvisible physical.1 physical.2)]
      exact physical.2
  have hedge (e : CollarCoordinate selected) :
      data.edge (qOf e).1 = e.1 := by
    apply Subtype.ext
    change FiniteSpecification.linkCrossPositiveEdge tau (qOf e).1.1 = e.1.1
    unfold qOf
    simp only
    exact Classical.choose_spec (hvisible e.1.1 e.2)
  exact data.endpointModeOfCollarMode selected
    (linkCombPhiFamily Lambda tau k hd D adj rho T x hcollar)
    (linkCombCollarMode Lambda tau k hd D H adj rho T hT x hcollar)
    qOf hedge

end

end YangMills.Gluelump.OneLink
