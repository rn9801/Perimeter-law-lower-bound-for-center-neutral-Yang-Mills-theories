/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ReflectedLine
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixedCore
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryBoxes

/-!
# Free-boundary-box certificates for mixed reflected screened lines

This file adapts the neutral mixed pairing from ReflectedLineMixedCore to the
ordinary free-boundary exhaustion.
-/

namespace YangMills.Gluelump.Propagation

open Filter Gauge Lattice.Cubic Wilson
open Endpoint
open StrongCoupling

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Two supported positive half-arms give an eventual mixed family
Cauchy--Schwarz certificate, with their reflected full lines as the two norm
squares. -/
theorem eventuallyLinkCrossingFamilyCauchySchwarz_reflectedMixed_of_support
    (rho : ContinuousUnitaryRepData G n)
    (Psi Xi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (z : Site d) (hz : z τ = 0) {y u : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (r : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hPsiCov : GaugeCovariantAt rho y Psi)
    (hXiCov : GaugeCovariantAt rho u Xi)
    (hPsi : Psi.SupportedInLinkPositiveHalf τ 0)
    (hXi : Xi.SupportedInLinkPositiveHalf τ 0)
    (hq : Endpoint.Path.SupportedInLinkPositiveHalf τ 0 q)
    (hr : Endpoint.Path.SupportedInLinkPositiveHalf τ 0 r) :
    EventuallyLinkCrossingFamilyCauchySchwarz (ι := Fin n) τ
      (reflectedMixedObservable rho Psi Xi τ 0 z hz q r)
      (screenedObservable rho (Psi.linkPullback τ 0) Psi
        (reflectedFullPath τ 0 z hz q))
      (screenedObservable rho (Xi.linkPullback τ 0) Xi
        (reflectedFullPath τ 0 z hz r)) := by
  obtain ⟨hinq, houtq⟩ := reflectedFullPath_sideSupport
    rho Psi τ 0 z hz q hPsi hq
  obtain ⟨hinr, houtr⟩ := reflectedFullPath_sideSupport
    rho Xi τ 0 z hz r hXi hr
  let OFH := reflectedMixedObservable rho Psi Xi τ 0 z hz q r
  let OFF := screenedObservable rho (Psi.linkPullback τ 0) Psi
    (reflectedFullPath τ 0 z hz q)
  let OHH := screenedObservable rho (Xi.linkPullback τ 0) Xi
    (reflectedFullPath τ 0 z hz r)
  filter_upwards
      [support_subset_freeBoundarySpecification_eventually τ OFH,
       support_subset_freeBoundarySpecification_eventually τ OFF,
       support_subset_freeBoundarySpecification_eventually τ OHH]
      with N hFHdyn hFFdyn hHHdyn
  let Λ := freeBoundarySpecification G d N τ
  have hecross : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hFHdyn (by
      dsimp only [OFH, reflectedMixedObservable]
      rw [screenedObservable_support]
      apply Finset.mem_union_right
      unfold reflectedMixedFullPath
      rw [Path.edgeSupport_comp]
      apply Finset.mem_union_right
      unfold crossingThenPath
      rw [Path.edgeSupport_comp]
      apply Finset.mem_union_left
      change crossingPositiveEdge z τ ∈
        ({crossingPositiveEdge z τ} : Finset (PositiveEdge d))
      simp), rfl, hz⟩
  let F := fun i => linkRestrictNegativeObservable Λ τ 0
    (freeBoundarySpecification_linkSymmetric N τ)
    (incomingHalfComponent rho (Psi.linkPullback τ 0)
      (reflectedIncomingPath τ 0 z hz q) i)
  let H := fun i => linkRestrictNegativeObservable Λ τ 0
    (freeBoundarySpecification_linkSymmetric N τ)
    (incomingHalfComponent rho (Xi.linkPullback τ 0)
      (reflectedIncomingPath τ 0 z hz r) i)
  refine ⟨F, H, ?_, ?_, ?_⟩
  · exact reflectedMixedFullPath_isGaugeFixedLinkFamilyPairing
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho Psi Xi z hz q r hPsiCov hXiCov hFHdyn hecross hinq hinr houtr
  · exact reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho Psi z hz q hPsiCov hFFdyn hecross hinq houtq
  · exact reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho Xi z hz r hXiCov hHHdyn hecross hinr houtr

end

end YangMills.Gluelump.Propagation
