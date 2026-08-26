/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ReflectedLineCore
import YangMills.StrongCoupling.InfiniteVolumeLinkCrossing

/-!
# Completed-box certificates for reflected screened lines

This file is the strong-coupling adapter for the neutral pointwise and finite-
specification constructions in ReflectedLineCore. It packages those exact
factorizations along the completed link-symmetric exhaustion.
-/

namespace YangMills.Gluelump.Propagation

open Filter Gauge Lattice.Cubic Wilson
open Endpoint
open StrongCoupling

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-! ## Passage to the completed link-symmetric exhaustion -/

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The distinguished crossing edge is explicitly recorded in the support of
the reflected full screened line. -/
theorem crossingPositiveEdge_mem_reflectedFullPath_support
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (z : Site d) (hz : z τ = 0) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y) :
    crossingPositiveEdge z τ ∈
      (screenedObservable rho (Psi.linkPullback τ 0) Psi
        (reflectedFullPath τ 0 z hz q)).support := by
  rw [screenedObservable_support]
  apply Finset.mem_union_right
  unfold reflectedFullPath
  rw [Path.edgeSupport_comp]
  apply Finset.mem_union_right
  unfold crossingThenPath
  rw [Path.edgeSupport_comp]
  apply Finset.mem_union_left
  change crossingPositiveEdge z τ ∈
    ({crossingPositiveEdge z τ} : Finset (PositiveEdge d))
  simp

/-- The exact fixed-slice reflected-line factorization persists eventually
along the completed link-symmetric exhaustion, and therefore is directly
usable by the infinite-volume family reflection-positivity engine. -/
theorem eventuallyLinkCrossingFamilyNormSquare_reflectedFullPath
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (z : Site d) (hz : z τ = 0) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hPsi : GaugeCovariantAt rho y Psi)
    (hin : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ 0
      ((incomingHalfComponent rho (Psi.linkPullback τ 0)
        (reflectedIncomingPath τ 0 z hz q) i).conj.linkTheta τ 0))
    (hout : ∀ i, (outgoingHalfComponent rho Psi
      (crossingThenPath τ z q) i).SupportedInLinkPositiveHalf τ 0) :
    EventuallyLinkCrossingFamilyNormSquare (ι := Fin n) τ
      (screenedObservable rho (Psi.linkPullback τ 0) Psi
        (reflectedFullPath τ 0 z hz q)) := by
  let O := screenedObservable rho (Psi.linkPullback τ 0) Psi
    (reflectedFullPath τ 0 z hz q)
  filter_upwards [support_subset_linkSymmetricSpecification_eventually τ O]
      with N hdyn
  let Λ := linkSymmetricSpecification G d N τ
  have hedynamic : crossingPositiveEdge z τ ∈ Λ.dynamicEdges :=
    hdyn (crossingPositiveEdge_mem_reflectedFullPath_support
      rho Psi τ z hz q)
  have hecross : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hedynamic, rfl, hz⟩
  refine ⟨fun i => linkRestrictNegativeObservable Λ τ 0
    (linkSymmetricSpecification_linkSymmetric N τ)
    (incomingHalfComponent rho (Psi.linkPullback τ 0)
      (reflectedIncomingPath τ 0 z hz q) i), ?_⟩
  exact reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
    Λ τ 0 (linkSymmetricSpecification_linkSymmetric N τ)
    rho Psi z hz q hPsi hdyn hecross hin hout

/-- Usable reflected-line certificate with the internal scalar-component
support obligations discharged from positive collar and path geometry. -/
theorem eventuallyLinkCrossingFamilyNormSquare_reflectedFullPath_of_support
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (z : Site d) (hz : z τ = 0) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hPsiCov : GaugeCovariantAt rho y Psi)
    (hPsi : Psi.SupportedInLinkPositiveHalf τ 0)
    (hq : Endpoint.Path.SupportedInLinkPositiveHalf τ 0 q) :
    EventuallyLinkCrossingFamilyNormSquare (ι := Fin n) τ
      (screenedObservable rho (Psi.linkPullback τ 0) Psi
        (reflectedFullPath τ 0 z hz q)) := by
  obtain ⟨hin, hout⟩ := reflectedFullPath_sideSupport
    rho Psi τ 0 z hz q hPsi hq
  exact eventuallyLinkCrossingFamilyNormSquare_reflectedFullPath
    rho Psi τ z hz q hPsiCov hin hout

end

end YangMills.Gluelump.Propagation
