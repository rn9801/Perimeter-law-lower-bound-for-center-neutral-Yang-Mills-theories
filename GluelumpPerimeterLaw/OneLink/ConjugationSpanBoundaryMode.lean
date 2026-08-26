/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConjugationSpanEndpointMode
import GluelumpPerimeterLaw.OneLink.ConcreteCombBoundaryMode

/-!
# The direct conjugation-span mode in link-boundary coordinates

This file transports the exact homogeneous mode of the direct
conjugation-span endpoint to the selected collar of a finite link-reflection
side and then into the actual crossing-feature family.  The construction is
pure finite-coordinate reindexing, so its degree and extraction cost depend
only on the fixed endpoint and not on the ambient finite specification.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson Endpoint RepresentationTheory
open Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The direct endpoint coordinates on the selected link-side collar. -/
def linkConjSpanPhiFamily
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k) (i : Fin r) :
    C((CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x) → G), ℂ) :=
  (conjSpanCombPhiCollarCoordinate hd sigma rho T x i).comp
    ⟨fun U e ↦ U (linkCombCollarEquiv Lambda tau k hd x hcollar e), by
      apply continuous_pi
      intro e
      exact continuous_apply _⟩

/-- On a split positive-side configuration, the reindexed collar family is
literally the direct endpoint evaluated on the one-sided full
configuration.  This is the fixed-slice identification needed to connect
the reflected screened observable to the abstract numerator. -/
theorem linkConjSpanPhiFamily_splitSide_eq
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (i : Fin r)
    (U : Gauge.LinkReflection.SideConfiguration G
      (Lambda.linkPositiveEdges tau k)) :
    linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar i
        (splitSideMeasurableEquiv (G := G)
          (linkCombSelected (m := m) Lambda tau k hd x) U).1 =
      conjSpanPhi hd sigma rho T x
        (Lambda.linkEvaluateSide tau k hLambda U) i := by
  let S := combEndpointCollar (m := m) hd x
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let V : S → G := fun e ↦
    (splitSideMeasurableEquiv (G := G) selected U).1
      (linkCombCollarEquiv Lambda tau k hd x hcollar e)
  change ((conjSpanPhi hd sigma rho T x).component i)
      (extendFromFinset S V) =
    ((conjSpanPhi hd sigma rho T x).component i)
      (Lambda.linkEvaluateSide tau k hLambda U)
  apply ((conjSpanPhi hd sigma rho T x).component i).dependsOn_support
  intro e he
  have heS : e ∈ S := by
    simpa [S] using he
  simp only [extendFromFinset, dif_pos heS]
  change U ⟨e, hcollar heS⟩ =
    Lambda.linkEvaluateSide tau k hLambda U e
  exact (Lambda.linkEvaluateSide_apply_of_mem
    tau k hLambda U e (hcollar heS)).symm

/-- The nonzero direct endpoint mode in the selected side-collar
coordinates of any finite specification containing the fixed collar. -/
noncomputable def linkConjSpanCollarMode
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k) :
    EndpointConjugateMode (matrixFeature sigma)
      (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
      (combEndpointDegree (m := m) hd x) := by
  simpa only [linkConjSpanPhiFamily] using
    reindexMatrixEndpointMode sigma
      (linkCombCollarEquiv Lambda tau k hd x hcollar)
      (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i)
      (conjSpanCombEndpointConjugateMode hd sigma rho T hT x)

/-- The direct mode embedded in the selected crossing-feature family of the
concrete finite-volume link decomposition.  Repeated crossing labels are
retained; choosing one visible label per collar edge is enough. -/
noncomputable def linkConjSpanEndpointCrossMode
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k) (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d)
    (hcollar : combEndpointCollar (m := m) hd x ⊆
      Lambda.linkPositiveEdges tau k)
    (hvisible : ∀ e ∈ combEndpointCollar (m := m) hd x,
      ∃ p : Lambda.linkCrossPlaquettes tau k,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    EndpointConjugateMode
      ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau k hLambda hclosed sigma).endpointFeature
        (linkCombSelected (m := m) Lambda tau k hd x))
      (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
      (combEndpointDegree (m := m) hd x) := by
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
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
    (linkConjSpanPhiFamily Lambda tau k hd sigma rho T x hcollar)
    (linkConjSpanCollarMode Lambda tau k hd sigma rho T hT x hcollar)
    qOf hedge

end

end YangMills.Gluelump.OneLink
