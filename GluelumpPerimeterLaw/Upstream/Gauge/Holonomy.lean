/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Lattice.Path
import YangMills.Gauge.Holonomy

/-! Additive cast-source identities for path support and holonomy. -/

namespace YangMills.Lattice.Cubic.Path

variable {d : ℕ} {x y z : Site d}

@[simp]
theorem edgeSupport_castSource (p : Path x y) (h : x = z) :
    edgeSupport (YangMills.Basic.OrientedPath.castSource p h) = edgeSupport p := by
  subst h
  rfl

end YangMills.Lattice.Cubic.Path

namespace YangMills.Gauge

open Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G]

@[simp]
theorem holonomy_castSource (A : Configuration d G) {w x z : Site d}
    (p : Path x z) (h : x = w) :
    holonomy A (YangMills.Basic.OrientedPath.castSource p h) = holonomy A p := by
  subst h
  rfl

end YangMills.Gauge
