/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.FiniteVolume
import YangMills.Wilson.Representation

/-! Additive cyclic character identities used by gluelump Wilson loops. -/

namespace YangMills.Wilson.ContinuousUnitaryRepData

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G]

/-- Cyclically moving one factor through a character does not change it. -/
theorem character_mul_comm (ρ : ContinuousUnitaryRepData G n) (g h : G) :
    ρ.character (g * h) = ρ.character (h * g) := by
  simp only [character, map_mul, Matrix.UnitaryGroup.mul_val]
  exact Matrix.trace_mul_comm _ _

/-- Cyclically moving one factor through a normalized character does not
change it. -/
theorem normalizedCharacter_mul_comm
    (ρ : ContinuousUnitaryRepData G n) (g h : G) :
    ρ.normalizedCharacter (g * h) = ρ.normalizedCharacter (h * g) := by
  simp only [normalizedCharacter, ρ.character_mul_comm]

end YangMills.Wilson.ContinuousUnitaryRepData
