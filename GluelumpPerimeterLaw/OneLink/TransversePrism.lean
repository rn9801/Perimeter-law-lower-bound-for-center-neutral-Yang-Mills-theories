/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.TransverseLoops
import YangMills.Gauge.LinkReflectionBridge

/-!
# One-link prisms over transverse endpoint loops

The strict one-link Taylor term is not purely representation theoretic.  Each
edge read by the endpoint must be the positive-layer tangential edge of a
plaquette crossing the screened link plane.  This is true because the endpoint
loops lie in the two-dimensional coordinate plane perpendicular to the arm.
The construction uses three pairwise distinct axes and therefore records
`3 ≤ d` explicitly.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Endpoint

noncomputable section

/-- An edge contained in an arm-perpendicular plane cannot point along the
arm. -/
theorem direction_ne_armAxis_of_endpoints_eq
    {d : ℕ} (hd : 3 ≤ d) (e : PositiveEdge d)
    (he : e.source (Geometry.armAxis hd) =
      e.target (Geometry.armAxis hd)) :
    e.direction ≠ Geometry.armAxis hd := by
  intro hdir
  rw [PositiveEdge.target] at he
  simp [step, SignedDirection.forward, SignedDirection.delta,
    unitVector, hdir] at he

/-- The unit plaquette obtained by extruding a tangential positive edge one
step backwards along the arm direction. -/
def transverseEdgePrismPlaquette
    {d : ℕ} (hd : 3 ≤ d) (e : PositiveEdge d)
    (he : e.source (Geometry.armAxis hd) =
      e.target (Geometry.armAxis hd)) : Plaquette d where
  base := e.source - unitVector (Geometry.armAxis hd)
  first := Geometry.armAxis hd
  second := e.direction
  distinct := direction_ne_armAxis_of_endpoints_eq hd e he |>.symm

@[simp]
theorem transverseEdgePrismPlaquette_base_arm
    {d : ℕ} (hd : 3 ≤ d) (e : PositiveEdge d)
    (he : e.source (Geometry.armAxis hd) =
      e.target (Geometry.armAxis hd)) :
    (transverseEdgePrismPlaquette hd e he).base
        (Geometry.armAxis hd) =
      e.source (Geometry.armAxis hd) - 1 := by
  simp [transverseEdgePrismPlaquette, unitVector]

/-- The positive-layer edge selected by the link-reflection decomposition of
the prism plaquette is exactly the original endpoint edge. -/
theorem linkCrossPositiveEdge_transverseEdgePrismPlaquette
    {d : ℕ} (hd : 3 ≤ d) (e : PositiveEdge d)
    (he : e.source (Geometry.armAxis hd) =
      e.target (Geometry.armAxis hd)) :
    FiniteSpecification.linkCrossPositiveEdge (Geometry.armAxis hd)
        (transverseEdgePrismPlaquette hd e he) = e := by
  unfold FiniteSpecification.linkCrossPositiveEdge
  simp only [transverseEdgePrismPlaquette, if_pos]
  congr 1
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [step, SignedDirection.forward, SignedDirection.delta, unitVector]
  · simp [step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hi]

/-- Every endpoint-collar edge is the positive tangential edge of a concrete
crossing plaquette.  This is the geometric input needed to turn a nonzero
endpoint coefficient into a cross-plane Taylor word. -/
theorem transverseLoop_support_has_prismPlaquette
    {d m : ℕ} (hd : 3 ≤ d) (x : Site d) (e : PositiveEdge d)
    (he : e ∈ basedLoopSupport (transverseLoop (m := m) hd x)) :
    ∃ p : Plaquette d,
      p.base (Geometry.armAxis hd) = x (Geometry.armAxis hd) - 1 ∧
      (p.first = Geometry.armAxis hd ∨
        p.second = Geometry.armAxis hd) ∧
      FiniteSpecification.linkCrossPositiveEdge
        (Geometry.armAxis hd) p = e ∧
      e ∈ p.boundary.edgeSupport := by
  have hplane := basedLoopSupport_transverseLoop_armPlane hd x e he
  let p := transverseEdgePrismPlaquette hd e (hplane.1.trans hplane.2.symm)
  refine ⟨p, ?_, Or.inl rfl, ?_, ?_⟩
  · simpa [p, hplane.1] using
      transverseEdgePrismPlaquette_base_arm hd e
        (hplane.1.trans hplane.2.symm)
  · exact linkCrossPositiveEdge_transverseEdgePrismPlaquette hd e _
  · rw [← linkCrossPositiveEdge_transverseEdgePrismPlaquette hd e
      (hplane.1.trans hplane.2.symm)]
    exact FiniteSpecification.linkCrossPositiveEdge_mem_boundary
      (Geometry.armAxis hd) p (Or.inl rfl)

/-- If the finite specification contains the perpendicular plaquettes through
the cutting plane, every transverse-collar edge is represented by an actual
cross-plaquette label.  The construction invokes
`transverseLoop_support_has_prismPlaquette`, so the requirement `3 ≤ d` is
genuine rather than hidden in a coordinate convention. -/
theorem transverseLoop_support_has_linkCrossPlaquette
    {d m : ℕ} {G : Type*} [Group G]
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d) (x : Site d) (k : ℤ)
    (hx : x (Geometry.armAxis hd) = k + 1)
    (hactive : ∀ p : Plaquette d,
      p.base (Geometry.armAxis hd) = k →
      (p.first = Geometry.armAxis hd ∨
        p.second = Geometry.armAxis hd) →
      p ∈ Λ.activePlaquettes) :
    ∀ e ∈ basedLoopSupport (transverseLoop (m := m) hd x),
      ∃ p : Λ.linkCrossPlaquettes (Geometry.armAxis hd) k,
        FiniteSpecification.linkCrossPositiveEdge
          (Geometry.armAxis hd) p.1 = e := by
  intro e he
  obtain ⟨p, hpbase, hpperp, hpedge, _hpboundary⟩ :=
    transverseLoop_support_has_prismPlaquette hd x e he
  have hpbase' : p.base (Geometry.armAxis hd) = k := by
    rw [hpbase, hx]
    omega
  refine ⟨⟨p, Finset.mem_filter.mpr
    ⟨hactive p hpbase' hpperp, hpbase', hpperp⟩⟩, hpedge⟩

end

end YangMills.Gluelump.OneLink
