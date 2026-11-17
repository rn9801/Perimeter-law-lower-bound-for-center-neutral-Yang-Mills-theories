/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ReflectionSupport
import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionCrossingFamily

/-!
# Gauge-fixed Gram certificates for split screened paths

A screened path cut at a link-reflection plane has one scalar half-amplitude
for each representation coordinate.  This file restricts the negative and
positive amplitudes to the two labelled side configurations and packages the
exact fixed-slice identity as a finite Gram-family certificate.

The statement applies equally to a straight segment, a bent path, or part of
a rectangle: the geometry needed by each application is reduced to the two
explicit positive-half support hypotheses below.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson
open Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Restrict a negative-half observable to the common positive-side label
space by first conjugating and reflecting it.  The two conjugations cancel
when the restriction is evaluated on a reflected configuration. -/
def linkRestrictNegativeObservable
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F : LocalObservable d G) :
    LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
  Λ.linkRestrictObservable τ k hΛ (F.conj.linkTheta τ k)

/-- Reflected collar/path support is sufficient for the incoming scalar
half-amplitude to belong to the positive link algebra. -/
theorem incomingHalfComponent_conj_linkTheta_supportedInLinkPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ)) {x z : Site d}
    (p : Lattice.Cubic.Path x z) (i : Fin n) (τ : Fin d) (k : ℤ)
    (hPhi : Endpoint.EdgeSet.SupportedInLinkPositiveHalf τ k
      (Phi.support.image (PositiveEdge.linkReflect τ k)))
    (hp : Endpoint.EdgeSet.SupportedInLinkPositiveHalf τ k
      (p.edgeSupport.image (PositiveEdge.linkReflect τ k))) :
    LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho Phi p i).conj.linkTheta τ k) := by
  change Endpoint.EdgeSet.SupportedInLinkPositiveHalf τ k
    ((Phi.support ∪ p.edgeSupport).image (PositiveEdge.linkReflect τ k))
  rw [Finset.image_union]
  exact Endpoint.EdgeSet.link_union hPhi hp

/-- Positive collar/path support is sufficient for the outgoing scalar
half-amplitude to belong to the positive link algebra. -/
theorem outgoingHalfComponent_supportedInLinkPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ)) {z y : Site d}
    (q : Lattice.Cubic.Path z y) (i : Fin n) (τ : Fin d) (k : ℤ)
    (hPsi : Psi.SupportedInLinkPositiveHalf τ k)
    (hq : Endpoint.Path.SupportedInLinkPositiveHalf τ k q) :
    LocalObservable.SupportedInLinkPositiveHalf τ k
      (outgoingHalfComponent rho Psi q i) := by
  exact Endpoint.EdgeSet.link_union hPsi hq

/-- On the identity-crossing slice, a negative-half observable is exactly its
reflected positive-side restriction. -/
theorem linkRestrictNegativeObservable_apply_assemble_fixed
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F : LocalObservable d G)
    (hF : (F.conj.linkTheta τ k).SupportedInLinkPositiveHalf τ k)
    (Uminus Uplus : LinkReflection.SideConfiguration G
      (Λ.linkPositiveEdges τ k)) :
    F (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))) =
      linkRestrictNegativeObservable Λ τ k hΛ F (1, Uminus) := by
  let W : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (Uminus, Uplus))
  have hrestrict := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (F.conj.linkTheta τ k) hF (LinkReflection.reflect W)
  rw [Λ.linkAssemble_reflect] at hrestrict
  have hinvOne : LinkReflection.invertCrossing
      (1 : LinkReflection.CrossingConfiguration G
        (Λ.linkCrossingEdges τ k)) = 1 := by
    funext e
    simp [LinkReflection.invertCrossing]
  simpa [linkRestrictNegativeObservable, W, LinkReflection.reflect,
    hinvOne, LocalObservable.conj, LocalObservable.linkTheta] using hrestrict

/-- A split screened path has the required finite Gram factorization after
the crossing links are fixed to the identity.  No half-line gauge-invariance
hypothesis occurs: only the full screened observable is gauge invariant. -/
theorem screenedObservable_comp_isGaugeFixedLinkFamilyPairing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x z y : Site d}
    (p : Lattice.Cubic.Path x z) (q : Lattice.Cubic.Path z y)
    (hPhi : GaugeCovariantAt rho x Phi)
    (hPsi : GaugeCovariantAt rho y Psi)
    (hdyn : (screenedObservable rho Phi Psi (p.comp q)).support ⊆
      Λ.dynamicEdges)
    (hin : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho Phi p i).conj.linkTheta τ k))
    (hout : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      (outgoingHalfComponent rho Psi q i)) :
    Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ
      (screenedObservable rho Phi Psi (p.comp q))
      (fun i => linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho Phi p i))
      (fun i => Λ.linkRestrictObservable τ k hΛ
        (outgoingHalfComponent rho Psi q i)) := by
  apply Λ.isGaugeFixedLinkFamilyPairing_of_gaugeInvariant τ k hΛ
    (screenedObservable rho Phi Psi (p.comp q))
    (fun i => linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho Phi p i))
    (fun i => Λ.linkRestrictObservable τ k hΛ
      (outgoingHalfComponent rho Psi q i))
    (screenedObservable_gaugeInvariant rho Phi Psi (p.comp q) hPhi hPsi)
    hdyn
  intro Uminus Uplus
  let A := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))
  rw [screenedObservable_apply, screenedValue_comp_eq_halfGram]
  apply Finset.sum_congr rfl
  intro i _hi
  have hleft := linkRestrictNegativeObservable_apply_assemble_fixed
    Λ τ k hΛ (incomingHalfComponent rho Phi p i) (hin i) Uminus Uplus
  have hright := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (outgoingHalfComponent rho Psi q i) (hout i)
    (1, (Uminus, Uplus))
  change star (incomingHalfComponent rho Phi p i A) *
      outgoingHalfComponent rho Psi q i A = _
  rw [hleft]
  simpa [A] using congrArg
    (fun w => star (linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho Phi p i) (1, Uminus)) * w) hright

end

end YangMills.Gluelump.Propagation
