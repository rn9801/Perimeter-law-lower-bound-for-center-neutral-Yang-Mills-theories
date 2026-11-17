/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Cubic

/-!
# Three explicit axes for gluelump endpoint geometry

The gluelump arm uses axis `0`; its endpoint loops use the transverse plane
spanned by axes `1` and `2`. Keeping these axes as explicit `Fin d` terms makes
the roadmap's `3 <= d` restriction a theorem hypothesis rather than an
implicit picture.
-/

namespace YangMills.Gluelump.Endpoint.Geometry

/-- The direction of the screened Wilson arm. -/
def armAxis {d : ℕ} (hd : 3 ≤ d) : Fin d :=
  ⟨0, by omega⟩

/-- The first transverse direction used by endpoint loops. -/
def transverseAxis₁ {d : ℕ} (hd : 3 ≤ d) : Fin d :=
  ⟨1, by omega⟩

/-- The second transverse direction used by endpoint loops. -/
def transverseAxis₂ {d : ℕ} (hd : 3 ≤ d) : Fin d :=
  ⟨2, by omega⟩

@[simp]
theorem armAxis_ne_transverseAxis₁ {d : ℕ} (hd : 3 ≤ d) :
    armAxis hd ≠ transverseAxis₁ hd := by
  intro h
  have hval := congrArg Fin.val h
  simp [armAxis, transverseAxis₁] at hval

@[simp]
theorem armAxis_ne_transverseAxis₂ {d : ℕ} (hd : 3 ≤ d) :
    armAxis hd ≠ transverseAxis₂ hd := by
  intro h
  have hval := congrArg Fin.val h
  simp [armAxis, transverseAxis₂] at hval

@[simp]
theorem transverseAxis₁_ne_transverseAxis₂ {d : ℕ} (hd : 3 ≤ d) :
    transverseAxis₁ hd ≠ transverseAxis₂ hd := by
  intro h
  have hval := congrArg Fin.val h
  simp [transverseAxis₁, transverseAxis₂] at hval

/-- The three axes used by the endpoint construction are pairwise distinct. -/
theorem axes_pairwise {d : ℕ} (hd : 3 ≤ d) :
    List.Pairwise (· ≠ ·)
      [armAxis hd, transverseAxis₁ hd, transverseAxis₂ hd] := by
  simp

end YangMills.Gluelump.Endpoint.Geometry
