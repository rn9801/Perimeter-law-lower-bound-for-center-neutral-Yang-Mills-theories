/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Path

/-! Additive path lemmas required by the standalone gluelump development. -/

namespace YangMills.Lattice.Cubic.Path

variable {d : ℕ} {w x y : Site d}

@[simp]
theorem directions_castSource (p : Path x y) (h : x = w) :
    directions (YangMills.Basic.OrientedPath.castSource p h) = directions p := by
  subst h
  rfl

/-- On the cubic lattice, the initial site and signed direction word uniquely
determine a typed path. -/
theorem ext_directions (p q : Path x y)
    (h : directions p = directions q) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp at h
  | cons p e ih =>
      cases q with
      | nil => simp at h
      | cons q f =>
          simp only [directions_cons] at h
          have hr := congrArg List.reverse h
          simp only [List.reverse_append, List.reverse_singleton,
            List.singleton_append, List.cons.injEq] at hr
          have hlast : e.1.direction = f.1.direction := hr.1
          have hprefix : directions p = directions q := by
            exact List.reverse_injective hr.2
          have hsource : e.1.source = f.1.source := by
            have ht : e.1.target = f.1.target :=
              e.2.2.trans f.2.2.symm
            change step e.1.source e.1.direction =
              step f.1.source f.1.direction at ht
            rw [hlast] at ht
            simpa [step] using ht
          have hmid : _ = _ := e.2.1.symm.trans (hsource.trans f.2.1)
          subst hmid
          have hpq : p = q := ih q hprefix
          subst q
          have hef : e = f := by
            apply Subtype.ext
            rw [show e.1 = SignedEdge.mk e.1.source e.1.direction by
              cases e.1; rfl]
            rw [show f.1 = SignedEdge.mk f.1.source f.1.direction by
              cases f.1; rfl]
            rw [hsource, hlast]
          subst f
          rfl

end YangMills.Lattice.Cubic.Path
