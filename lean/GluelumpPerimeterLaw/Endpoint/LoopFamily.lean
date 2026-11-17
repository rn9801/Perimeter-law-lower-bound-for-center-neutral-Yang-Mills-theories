/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.Holonomy

/-!
# Finite families of based endpoint loops

This module records the geometry-only API shared by axial and direct
holonomy endpoint constructions.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

variable {d m : ℕ} {G : Type*} [Group G]

/-- The union of the supports of a finite family of based endpoint loops. -/
def basedLoopSupport {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x) : Finset (PositiveEdge d) :=
  Finset.univ.biUnion fun i => (q i).edgeSupport

/-- The based loops allow independent prescribed holonomies. -/
def BasedLoopHolonomySurjective {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x) : Prop :=
  ∀ u : Fin m → G, ∃ A : Configuration d G,
    ∀ i, holonomy A (q i) = u i

end YangMills.Gluelump.Endpoint
