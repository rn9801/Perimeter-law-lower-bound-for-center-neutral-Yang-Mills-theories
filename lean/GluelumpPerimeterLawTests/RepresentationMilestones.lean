/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConjugationSpanEndpointMode
import GluelumpPerimeterLaw.Endpoint.ConjugationSpanScreenedWilsonLine

/-!
# Gluelump representation-milestone regressions

Focused axiom audits for the conjugation-span, quotient, and tensor-generation
milestones.  Keeping this separate from the full gluelump regression avoids
rebuilding the propagation and one-link developments when only the
representation-theory interface changes.
-/

namespace YangMills.Tests.GluelumpRepresentationMilestones

open YangMills.Gluelump

#print axioms RepresentationTheory.conjSpanRep_kernelIsCenter
#print axioms RepresentationTheory.conjSpanSelfDual
#print axioms RepresentationTheory.centerQuotient_injective_of_kernelIsCenter
#print axioms RepresentationTheory.coordinateUnitaryRepEquiv
#print axioms RepresentationTheory.faithful_selfDual_tensorPower_mapsTo_rep
#print axioms RepresentationTheory.hilbertConjSpanCoordinateEquiv
#print axioms RepresentationTheory.conjSpanCenterQuotientUnitaryRepData_injective
#print axioms RepresentationTheory.conjSpanCenterQuotientSelfDual
#print axioms RepresentationTheory.dualUnitaryRepEquiv
#print axioms RepresentationTheory.centerNeutral_exists_conjSpanIntertwiner
#print axioms RepresentationTheory.centerNeutral_iff_exists_conjSpanIntertwiner
#print axioms Endpoint.continuousRepresentationScreeningMultilinearForm_equivariant
#print axioms Endpoint.conjSpanPhi_not_identically_zero
#print axioms Endpoint.conjSpanScreenedWilsonLine_gaugeInvariant
#print axioms Endpoint.linkTheta_conjSpanScreenedWilsonLine_apply
#print axioms OneLink.doubledSwapTranspose_feature
#print axioms OneLink.conjSpanCombPhiCollarCoordinate_homogeneous
#print axioms OneLink.conjSpanCombEndpointConjugateMode

section PrimalTargetType

open Representation YangMills.Wilson

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  {n p : ℕ}

/-- Regression guard: the operational screening map targets the Wilson
representation itself, not its algebraic dual. -/
example (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G p)
    (hcenter : RepresentationTheory.CenterNeutral
      (RepresentationTheory.asRepresentation rho)) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
      (RepresentationTheory.tensorPower
        (RepresentationTheory.conjSpanRep sigma) m)
        (RepresentationTheory.asRepresentation rho), T ≠ 0 :=
  RepresentationTheory.centerNeutral_exists_conjSpanIntertwiner
    sigma hsigma rho hcenter

end PrimalTargetType

end YangMills.Tests.GluelumpRepresentationMilestones
