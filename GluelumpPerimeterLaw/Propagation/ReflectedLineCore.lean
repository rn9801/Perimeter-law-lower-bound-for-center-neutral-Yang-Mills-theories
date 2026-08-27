/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Reflection
import GluelumpPerimeterLaw.Propagation.ScreenedPathCertificate

/-!
# Explicit reflected screened lines

Starting from a path in the positive half-lattice, reflect and reverse it to
obtain the negative half.  A single perpendicular edge joins the two halves.
The endpoint on the negative side is the reflected pullback of the positive
endpoint.  These choices make the two Gram vectors agree exactly after the
crossing edge is fixed to the identity.
-/

namespace YangMills.Gluelump.Propagation

open Filter Gauge Lattice.Cubic Wilson
open Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The positive step from a site on `x τ = k` is reflected back to that
site by the link plane `x τ = k + 1/2`. -/
theorem linkReflection_step_forward_eq_of_coord
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k) :
    linkReflection τ k (step z (.forward τ)) = z := by
  ext i
  by_cases hi : i = τ
  · subst i
    rw [linkReflection_apply_eq]
    simp [step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
    omega
  · rw [linkReflection_apply_ne hi]
    simp [step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hi]

/-- Link reflection maps the recorded edge support of a typed path by the
stored-edge link involution. -/
@[simp]
theorem edgeSupport_linkReflect
    {x y : Site d} (τ : Fin d) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.linkReflect τ k).edgeSupport =
      p.edgeSupport.image (PositiveEdge.linkReflect τ k) := by
  induction p with
  | nil =>
      unfold Path.linkReflect Path.translate Path.siteReflect
      rw [Prefunctor.mapPath_nil (siteReflectionPrefunctor τ k),
        Path.edgeSupport_nil]
      change Path.edgeSupport (.nil : Lattice.Cubic.Path
        (Lattice.Cubic.translate (unitVector τ) (siteReflection τ k x))
        (Lattice.Cubic.translate (unitVector τ) (siteReflection τ k x))) = ∅
      rfl
  | cons p e ih =>
      unfold Path.linkReflect Path.translate Path.siteReflect at ih ⊢
      rw [Prefunctor.mapPath_cons (siteReflectionPrefunctor τ k) p e]
      change Path.edgeSupport
          (((translationPrefunctor (unitVector τ)).mapPath
            ((siteReflectionPrefunctor τ k).mapPath p)).cons
            ((translationPrefunctor (unitVector τ)).map
              ((siteReflectionPrefunctor τ k).map e))) = _
      rw [Path.edgeSupport_cons]
      simp only [Path.edgeSupport_cons, Finset.image_insert]
      congr 1
      · simpa [linkReflectionPrefunctor] using
          (positive_linkReflectionPrefunctor_map τ k e)

/-- Reversing a typed path does not change the set of stored links it reads. -/
@[simp]
theorem edgeSupport_reverse {x y : Site d} (p : Lattice.Cubic.Path x y) :
    Path.edgeSupport p.reverse = p.edgeSupport := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Quiver.Path.reverse.eq_def, Path.edgeSupport_comp, ih,
        Quiver.Hom.toPath, Path.edgeSupport_cons, Path.edgeSupport_nil,
        Path.edgeSupport_cons]
      rw [show (Quiver.reverse e).1.positive = e.1.positive by
        exact SignedEdge.positive_reverse e.1]
      simp [Finset.union_comm]

/-- Reverse the reflected positive half-path and cast its endpoint to the
negative endpoint of the distinguished crossing edge. -/
def reflectedIncomingPath (τ : Fin d) (k : ℤ) (z : Site d)
    (hz : z τ = k) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y) :
    Lattice.Cubic.Path (linkReflection τ k y) z :=
  YangMills.Basic.OrientedPath.castTarget
    ((q.linkReflect τ k).reverse)
    (linkReflection_step_forward_eq_of_coord τ k z hz)

/-- The distinguished crossing edge followed by the chosen positive
half-path. -/
def crossingThenPath (τ : Fin d) (z : Site d) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y) :
    Lattice.Cubic.Path z y :=
  (edgeFrom z (.forward τ)).toPath.comp q

/-- The centered full path obtained by joining a reflected negative half to
the crossing edge and positive half. -/
def reflectedFullPath (τ : Fin d) (k : ℤ) (z : Site d)
    (hz : z τ = k) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y) :
    Lattice.Cubic.Path (linkReflection τ k y) y :=
  (reflectedIncomingPath τ k z hz q).comp (crossingThenPath τ z q)

/-- Reflecting the recorded incoming support back to the positive side
recovers exactly the support of the original positive half-path. -/
theorem reflectedIncomingPath_support_image_linkReflect
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path (step z (.forward τ)) y) :
    (reflectedIncomingPath τ k z hz q).edgeSupport.image
        (PositiveEdge.linkReflect τ k) = q.edgeSupport := by
  unfold reflectedIncomingPath
  rw [Path.edgeSupport_castTarget, edgeSupport_reverse,
    edgeSupport_linkReflect, Finset.image_image]
  simp [Function.comp_def]

/-- The positive crossing step followed by a positive-side path remains in
the link-positive algebra. -/
theorem crossingThenPath_supportedInLinkPositiveHalf
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hq : Endpoint.Path.SupportedInLinkPositiveHalf τ k q) :
    Endpoint.Path.SupportedInLinkPositiveHalf τ k
      (crossingThenPath τ z q) := by
  intro e he
  unfold crossingThenPath at he
  rw [Path.edgeSupport_comp] at he
  rcases Finset.mem_union.mp he with he | he
  · change e ∈ ({⟨z, τ⟩} : Finset (PositiveEdge d)) at he
    simp only [Finset.mem_singleton] at he
    subst e
    simp [PositiveEdge.target, step, SignedDirection.delta,
      SignedDirection.forward, unitVector, hz]
  · exact hq e he

/-- Positive collar and path support discharge both side-support hypotheses
of the reflected-line Gram certificate. -/
theorem reflectedFullPath_sideSupport
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hPsi : Psi.SupportedInLinkPositiveHalf τ k)
    (hq : Endpoint.Path.SupportedInLinkPositiveHalf τ k q) :
    (∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i).conj.linkTheta τ k)) ∧
    (∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      (outgoingHalfComponent rho Psi (crossingThenPath τ z q) i)) := by
  constructor
  · intro i
    apply incomingHalfComponent_conj_linkTheta_supportedInLinkPositiveHalf
    · change Endpoint.EdgeSet.SupportedInLinkPositiveHalf τ k
        ((Psi.support.image (PositiveEdge.linkReflect τ k)).image
          (PositiveEdge.linkReflect τ k))
      rw [Finset.image_image]
      simpa [Function.comp_def] using hPsi
    · rw [reflectedIncomingPath_support_image_linkReflect]
      exact hq
  · intro i
    exact outgoingHalfComponent_supportedInLinkPositiveHalf
      rho Psi (crossingThenPath τ z q) i τ k hPsi
      (crossingThenPath_supportedInLinkPositiveHalf τ k z hz q hq)

@[simp]
theorem holonomy_reflectedIncomingPath_linkReflectConfiguration
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (A : Configuration d G) :
    holonomy (linkReflectConfiguration τ k A)
        (reflectedIncomingPath τ k z hz q) =
      (holonomy A q)⁻¹ := by
  unfold reflectedIncomingPath
  rw [holonomy_castTarget, holonomy_reverse]
  have h := holonomy_linkReflectConfiguration τ k
    (linkReflectConfiguration τ k A) q
  rw [linkReflectConfiguration_linkReflectConfiguration] at h
  rw [← h]

/-- The incoming Gram coordinate on a reflected configuration is exactly the
outgoing Gram coordinate on the original positive-half configuration. -/
theorem incomingHalfComponent_reflected_eq_outgoingHalfComponent
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (i : Fin n) (A : Configuration d G) :
    incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i
        (linkReflectConfiguration τ k A) =
      outgoingHalfComponent rho Psi q i A := by
  rw [incomingHalfComponent_apply, outgoingHalfComponent_apply,
    LocalField.linkPullback_apply,
    linkReflectConfiguration_linkReflectConfiguration,
    holonomy_reflectedIncomingPath_linkReflectConfiguration]
  simp

/-- The stored positive edge underlying the distinguished crossing step. -/
def crossingPositiveEdge (z : Site d) (τ : Fin d) : PositiveEdge d :=
  ⟨z, τ⟩

/-- Fixing the distinguished crossing edge to the identity removes it from
the outgoing half holonomy. -/
theorem outgoingHalfComponent_crossingThenPath_eq_of_crossing_one
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (z : Site d) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (i : Fin n) (A : Configuration d G)
    (hcross : A (crossingPositiveEdge z τ) = 1) :
    outgoingHalfComponent rho Psi (crossingThenPath τ z q) i A =
      outgoingHalfComponent rho Psi q i A := by
  rw [outgoingHalfComponent_apply, outgoingHalfComponent_apply]
  unfold crossingThenPath
  rw [holonomy_comp, holonomy_toPath]
  change representationAction rho (A (crossingPositiveEdge z τ) * holonomy A q)
      (Psi A) i = _
  rw [hcross, one_mul]

/-- On one labelled positive side, the reflected incoming Gram coordinate is
the outgoing coordinate of the original positive half-path. -/
theorem linkRestrictNegative_reflectedIncoming_eq_outgoing_on_side
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z τ = k) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y) (i : Fin n)
    (hin : LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i).conj.linkTheta τ k))
    (U : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) :
    linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho (Psi.linkPullback τ k)
          (reflectedIncomingPath τ k z hz q) i) (1, U) =
      outgoingHalfComponent rho Psi q i
        (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, U)))) := by
  let Win : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (U, 1))
  let Wout : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (1, U))
  have hrestrict := linkRestrictNegativeObservable_apply_assemble_fixed
    Λ τ k hΛ
    (incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i) hin U 1
  have hreflect := Λ.linkAssemble_reflect τ k hΛ Wout
  have hinvOne : LinkReflection.invertCrossing
      (1 : LinkReflection.CrossingConfiguration G
        (Λ.linkCrossingEdges τ k)) = 1 := by
    funext e
    simp [LinkReflection.invertCrossing]
  have hWin : Λ.evaluate (Λ.linkAssemble τ k hΛ Win) =
      linkReflectConfiguration τ k
        (Λ.evaluate (Λ.linkAssemble τ k hΛ Wout)) := by
    simpa [Win, Wout, LinkReflection.reflect, hinvOne] using hreflect
  rw [← hrestrict]
  change incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i
      (Λ.evaluate (Λ.linkAssemble τ k hΛ Win)) = _
  rw [hWin]
  exact incomingHalfComponent_reflected_eq_outgoingHalfComponent
    rho Psi τ k z hz q i _

/-- The explicit reflected screened line is a finite Gram norm square on the
gauge-fixed crossing slice. -/
theorem reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z τ = k) {y : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hPsi : GaugeCovariantAt rho y Psi)
    (hdyn : (screenedObservable rho (Psi.linkPullback τ k) Psi
        (reflectedFullPath τ k z hz q)).support ⊆ Λ.dynamicEdges)
    (hecross : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ k)
    (hin : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i).conj.linkTheta τ k))
    (hout : ∀ i, (outgoingHalfComponent rho Psi
      (crossingThenPath τ z q) i).SupportedInLinkPositiveHalf τ k) :
    Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ
      (screenedObservable rho (Psi.linkPullback τ k) Psi
        (reflectedFullPath τ k z hz q))
      (fun i => linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho (Psi.linkPullback τ k)
          (reflectedIncomingPath τ k z hz q) i))
      (fun i => linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho (Psi.linkPullback τ k)
          (reflectedIncomingPath τ k z hz q) i)) := by
  apply Λ.isGaugeFixedLinkFamilyPairing_of_gaugeInvariant τ k hΛ
    (screenedObservable rho (Psi.linkPullback τ k) Psi
      (reflectedFullPath τ k z hz q))
    (fun i => linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i))
    (fun i => linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i))
    (screenedObservable_gaugeInvariant rho (Psi.linkPullback τ k) Psi
      (reflectedFullPath τ k z hz q)
      (GaugeCovariantAt.linkPullback rho y Psi hPsi τ k) hPsi)
    hdyn
  intro Uminus Uplus
  let A := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))
  let B := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, Uplus)))
  rw [screenedObservable_apply]
  change screenedValue rho (Psi.linkPullback τ k) Psi
      ((reflectedIncomingPath τ k z hz q).comp
        (crossingThenPath τ z q)) A = _
  rw [screenedValue_comp_eq_halfGram]
  apply Finset.sum_congr rfl
  intro i _hi
  have hleft := linkRestrictNegativeObservable_apply_assemble_fixed
    Λ τ k hΛ
    (incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i) (hin i) Uminus Uplus
  have houtA := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (outgoingHalfComponent rho Psi (crossingThenPath τ z q) i) (hout i)
    (1, (Uminus, Uplus))
  have houtB := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (outgoingHalfComponent rho Psi (crossingThenPath τ z q) i) (hout i)
    (1, (1, Uplus))
  have hcrossB : B (crossingPositiveEdge z τ) = 1 := by
    exact Λ.linkCrossingEdge_value_fixed τ k hΛ (1, Uplus)
      (crossingPositiveEdge z τ) hecross
  have hdrop := outgoingHalfComponent_crossingThenPath_eq_of_crossing_one
    rho Psi τ z q i B hcrossB
  have hmatch := linkRestrictNegative_reflectedIncoming_eq_outgoing_on_side
    Λ τ k hΛ rho Psi z hz q i (hin i) Uplus
  change star (incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i A) *
      outgoingHalfComponent rho Psi (crossingThenPath τ z q) i A = _
  rw [hleft]
  have houtAB : outgoingHalfComponent rho Psi
      (crossingThenPath τ z q) i A =
      outgoingHalfComponent rho Psi (crossingThenPath τ z q) i B := by
    rw [houtA, houtB]
  rw [houtAB, hdrop, ← hmatch]

end

end YangMills.Gluelump.Propagation
