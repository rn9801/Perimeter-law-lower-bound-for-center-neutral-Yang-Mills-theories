/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Geometry
import YangMills.Gauge.Holonomy

/-! # The distinguished one-bond Wilson-arm path -/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G]

/-- The forward unit bond along the distinguished Wilson-arm axis. -/
def armBondPath (hd : 3 ≤ d) (x : Site d) :
    Lattice.Cubic.Path x
      (Lattice.Cubic.Path.advance x (.forward (Geometry.armAxis hd)) 1) :=
  Lattice.Cubic.Path.straight x (.forward (Geometry.armAxis hd)) 1

/-- Holonomy on the distinguished unit bond is its stored positive-edge
variable. -/
@[simp]
theorem holonomy_armBondPath
    (hd : 3 ≤ d) (x : Site d) (Q : Configuration d G) :
    holonomy Q (armBondPath hd x) = Q ⟨x, Geometry.armAxis hd⟩ := by
  simp [armBondPath, Lattice.Cubic.Path.straight, holonomy, edgeFrom]
  change signedEdgeValue Q ⟨x, .forward (Geometry.armAxis hd)⟩ = _
  exact signedEdgeValue_forward Q x (Geometry.armAxis hd)

end YangMills.Gluelump.Endpoint
