/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflection
import GluelumpPerimeterLaw.Upstream.Gauge.InfiniteReflection

/-!
# Neutral coordinate-axis basepoints

This small module isolates the coordinate point used by straight, corner,
and rectangle geometry from any measure or thermodynamic-limit construction.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic

/-- The canonical point `r e_a` on a coordinate axis. -/
def axisPoint {d : ℕ} (a : Fin d) (r : ℕ) : Site d :=
  r • unitVector a

@[simp]
theorem axisPoint_apply_self {d : ℕ} (a : Fin d) (r : ℕ) :
    axisPoint a r a = r := by
  simp [axisPoint, unitVector]

@[simp]
theorem axisPoint_apply_ne {d : ℕ} {a b : Fin d} (hab : b ≠ a) (r : ℕ) :
    axisPoint a r b = 0 := by
  simp [axisPoint, unitVector, hab]

@[simp]
theorem diagonalReflection_zero_fixed {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) :
    diagonalReflection a b 0 (0 : Site d) = 0 := by
  ext i
  by_cases hia : i = a
  · subst i
    simp
  · by_cases hib : i = b
    · subst i
      simp [hab]
    · simp [diagonalReflection, hia, hib]

@[simp]
theorem directions_siteReflect {d : ℕ} {x y : Site d}
    (a : Fin d) (k : ℤ) (p : Lattice.Cubic.Path x y) :
    (p.siteReflect a k).directions =
      p.directions.map (SignedDirection.siteReflect a) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Path.directions ((siteReflectionPrefunctor a k).mapPath p) = _ at ih
      change Path.directions (((siteReflectionPrefunctor a k).mapPath p).cons
        ((siteReflectionPrefunctor a k).map e)) = _
      rw [Path.directions_cons, ih]
      rw [Path.directions_cons, List.map_append, List.map_singleton]
      rfl

@[simp]
theorem directions_diagonalReflect {d : ℕ} {x y : Site d}
    {a b : Fin d} (hab : a ≠ b) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.diagonalReflect a b hab k).directions =
      p.directions.map (SignedDirection.diagonalReflect a b) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Path.directions
        ((diagonalReflectionPrefunctor a b hab k).mapPath p) = _ at ih
      change Path.directions
        (((diagonalReflectionPrefunctor a b hab k).mapPath p).cons
          ((diagonalReflectionPrefunctor a b hab k).map e)) = _
      rw [Path.directions_cons, ih]
      rw [Path.directions_cons, List.map_append, List.map_singleton]
      rfl

end YangMills.Gluelump.Propagation
