/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.FiniteVolume
import YangMills.Gauge.SiteReflection

/-! Additive endpoint geometry for site reflection. -/

namespace YangMills.Lattice.Cubic.PositiveEdge

/-- Reflection sends the unordered pair of endpoints of a stored positive
edge to the reflected unordered pair.  The order is reversed exactly for an
edge perpendicular to the reflection plane. -/
theorem siteReflect_endpoints {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    ((e.siteReflect τ k).source = siteReflection τ k e.source ∧
        (e.siteReflect τ k).target = siteReflection τ k e.target) ∨
      ((e.siteReflect τ k).source = siteReflection τ k e.target ∧
        (e.siteReflect τ k).target = siteReflection τ k e.source) := by
  by_cases hdir : e.direction = τ
  · right
    subst τ
    simp only [siteReflect, if_pos]
    constructor
    · trivial
    · change step (siteReflection e.direction k e.target)
          (.forward e.direction) = siteReflection e.direction k e.source
      rw [show e.target = step e.source (.forward e.direction) by rfl,
        siteReflection_step]
      simp only [SignedDirection.siteReflect, SignedDirection.forward, if_true]
      change step (step (siteReflection e.direction k e.source)
        (.backward e.direction)) (.forward e.direction) = _
      exact step_reverse (siteReflection e.direction k e.source)
        (.backward e.direction)
  · left
    simp only [siteReflect, hdir, if_false]
    constructor
    · trivial
    · change step (siteReflection τ k e.source) (.forward e.direction) =
        siteReflection τ k e.target
      rw [show e.target = step e.source (.forward e.direction) by rfl,
        siteReflection_step]
      congr 1
      simp only [SignedDirection.siteReflect, SignedDirection.forward,
        hdir, if_false]

end YangMills.Lattice.Cubic.PositiveEdge
