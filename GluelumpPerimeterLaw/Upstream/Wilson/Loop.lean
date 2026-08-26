/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Wilson.Representation
import YangMills.Wilson.Loop

/-! Additive cyclic-basepoint identity for Wilson loops. -/

namespace YangMills.Wilson.ContinuousUnitaryRepData

open YangMills.Gauge YangMills.Lattice.Cubic

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- A Wilson loop is independent of the chosen cut in a two-piece closed
path.  This is the precise cyclic-basepoint identity used for rectangles. -/
theorem wilsonLoop_comp_comm (ρ : ContinuousUnitaryRepData G n)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (q : Lattice.Cubic.Path y x) (A : Configuration d G) :
    ρ.wilsonLoop (p.comp q) A = ρ.wilsonLoop (q.comp p) A := by
  simp only [wilsonLoop_apply, holonomy_comp]
  exact ρ.normalizedCharacter_mul_comm _ _

end YangMills.Wilson.ContinuousUnitaryRepData
