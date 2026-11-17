/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.TransverseLoops

/-!
# Canonical transverse loop family

The repository already contains a deterministic family with exactly the
properties for which the new roadmap proposes a separated comb: nested
unit-height rectangles in the two transverse axes, with a distinct far edge
for every loop.  A sparse configuration supported on those far edges realizes
arbitrary holonomies independently.  This file exposes that proved
construction under the roadmap-facing comb API instead of duplicating the
geometry with a second path convention.

The nested-rectangle version has the same shared-spine interpretation and a
tighter support bound (`m` rather than `2*m`).  Downstream endpoint code may
depend only on the declarations in this file.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

/-- The canonical roadmap-facing transverse loop family. -/
abbrev combLoops {d m : ℕ} (hd : 3 ≤ d) (x : Site d) (i : Fin m) :
    Lattice.Cubic.Path x x :=
  transverseLoop hd x i

/-- The independently assignable chord/far edge of the `i`th loop. -/
abbrev combLoopChord {d m : ℕ} (hd : 3 ≤ d) (x : Site d)
    (i : Fin m) : PositiveEdge d :=
  transverseLoopFarEdge hd x i

/-- Sparse comb configuration realizing prescribed loop holonomies. -/
abbrev combLoopConfiguration {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) : Configuration d G :=
  transverseLoopConfiguration hd x u

/-- The distinguished comb chords are pairwise distinct. -/
theorem combLoopChord_injective {d m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    Function.Injective (combLoopChord hd x : Fin m → PositiveEdge d) :=
  transverseLoopFarEdge_injective hd x

/-- Each distinguished chord carries its prescribed group element. -/
@[simp]
theorem combLoopConfiguration_chord {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) (i : Fin m) :
    combLoopConfiguration hd x u (combLoopChord hd x i) = u i :=
  transverseLoopConfiguration_farEdge hd x u i

/-- The explicit sparse configuration realizes every prescribed tuple of
comb-loop holonomies. -/
theorem combLoops_realize_holonomies
    {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) (i : Fin m) :
    holonomy (combLoopConfiguration hd x u) (combLoops hd x i) = u i :=
  holonomy_transverseLoopConfiguration_transverseLoop hd x u i

/-- Prominent surjectivity form consumed by endpoint nonvanishing. -/
theorem combLoops_holonomySurjective
    {d m : ℕ} {G : Type*} [Group G] (hd : 3 ≤ d) (x : Site d) :
    BasedLoopHolonomySurjective (G := G) (combLoops (m := m) hd x) :=
  transverseLoop_holonomySurjective hd x

/-- Every comb edge lies in the coordinate plane perpendicular to the Wilson
arm. -/
theorem basedLoopSupport_combLoops_armPlane {d m : ℕ}
    (hd : 3 ≤ d) (x : Site d) :
    ∀ e ∈ basedLoopSupport (combLoops (m := m) hd x),
      e.source (Geometry.armAxis hd) = x (Geometry.armAxis hd) ∧
      e.target (Geometry.armAxis hd) = x (Geometry.armAxis hd) :=
  basedLoopSupport_transverseLoop_armPlane hd x

/-- The first transverse coordinate lies in the explicit collar
`[x, x+m]`. -/
theorem basedLoopSupport_combLoops_transverseAxis₁_bounds
    {d m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    ∀ e ∈ basedLoopSupport (combLoops (m := m) hd x),
      x (Geometry.transverseAxis₁ hd) ≤
          e.source (Geometry.transverseAxis₁ hd) ∧
      e.source (Geometry.transverseAxis₁ hd) ≤
          x (Geometry.transverseAxis₁ hd) + m ∧
      x (Geometry.transverseAxis₁ hd) ≤
          e.target (Geometry.transverseAxis₁ hd) ∧
      e.target (Geometry.transverseAxis₁ hd) ≤
          x (Geometry.transverseAxis₁ hd) + m :=
  basedLoopSupport_transverseLoop_transverseAxis₁_bounds hd x

/-- The paper places the comb's short direction in the rectangle plane;
that coordinate has width one at every tensor degree. -/
theorem basedLoopSupport_combLoops_transverseAxis₂_bounds
    {d m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    ∀ e ∈ basedLoopSupport (combLoops (m := m) hd x),
      x (Geometry.transverseAxis₂ hd) ≤ e.source (Geometry.transverseAxis₂ hd) ∧
      e.source (Geometry.transverseAxis₂ hd) ≤ x (Geometry.transverseAxis₂ hd) + 1 ∧
      x (Geometry.transverseAxis₂ hd) ≤ e.target (Geometry.transverseAxis₂ hd) ∧
      e.target (Geometry.transverseAxis₂ hd) ≤ x (Geometry.transverseAxis₂ hd) + 1 :=
  basedLoopSupport_transverseLoop_transverseAxis₂_bounds hd x

/-- Translation sends the canonical loop template to the same template at
the translated basepoint. -/
theorem translate_combLoops {d m : ℕ} (hd : 3 ≤ d)
    (v x : Site d) (i : Fin m) :
    Path.translate v (combLoops hd x i) =
      combLoops hd (Lattice.Cubic.translate v x) i := by
  apply Path.ext_directions
  simp [combLoops, transverseLoop, Path.directions_rectangleBoundary]

end

end YangMills.Gluelump.Endpoint
