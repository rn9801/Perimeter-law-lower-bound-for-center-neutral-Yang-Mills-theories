/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.AntiDiagonalClosingCore
import GluelumpPerimeterLaw.Propagation.CanonicalGeometryBase
import GluelumpPerimeterLaw.Propagation.DiagonalBendingCore
import GluelumpPerimeterLaw.Endpoint.TransverseLoops

/-!
# Direct conjugation-span corner geometry

The physical straight line of length `s+t` naturally runs from
`-s e_a` to `t e_a`.  We bend it through the affine diagonal plane
`x_a-x_b=-s` and close it through the anti-diagonal plane
`x_a+x_b=t`.  The resulting loop is the boundary of a translated
`(s+t) × (s+t)` coordinate square.

Keeping the asymmetric pair `(s,t)` is what lets the even and odd members of
the physical-length family enter literally, without a length-dependent
renormalization or a second straight-line sequence.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint

noncomputable section

variable {d : ℕ}

/-! ## Affine square vertices and paths -/

/-- The left endpoint `-s e_a` of the physical straight line. -/
def conjSpanCornerOriginSite {d : ℕ} (a : Fin d) (s : ℕ) : Site d :=
  (-(s : ℤ)) • unitVector a

/-- The right endpoint `t e_a` of the physical straight line. -/
def conjSpanCornerFarSite {d : ℕ} (a : Fin d) (t : ℕ) : Site d :=
  (t : ℤ) • unitVector a

/-- The upper-left vertex `-s e_a + (s+t)e_b`. -/
def conjSpanCornerUpperLeftSite {d : ℕ}
    (a b : Fin d) (s t : ℕ) : Site d :=
  Lattice.Cubic.translate ((s + t : ℕ) • unitVector b)
    (conjSpanCornerOriginSite a s)

/-- The upper-right vertex `t e_a + (s+t)e_b`. -/
def conjSpanCornerUpperRightSite {d : ℕ}
    (a b : Fin d) (s t : ℕ) : Site d :=
  Lattice.Cubic.translate ((s + t : ℕ) • unitVector b)
    (conjSpanCornerFarSite a t)

@[simp]
theorem conjSpanCornerOriginSite_apply_self {d : ℕ}
    (a : Fin d) (s : ℕ) :
    conjSpanCornerOriginSite a s a = -(s : ℤ) := by
  simp [conjSpanCornerOriginSite, unitVector]

@[simp]
theorem conjSpanCornerOriginSite_apply_ne {d : ℕ}
    {a b : Fin d} (hab : b ≠ a) (s : ℕ) :
    conjSpanCornerOriginSite a s b = 0 := by
  simp [conjSpanCornerOriginSite, unitVector, hab]

@[simp]
theorem conjSpanCornerFarSite_apply_self {d : ℕ}
    (a : Fin d) (t : ℕ) :
    conjSpanCornerFarSite a t a = t := by
  simp [conjSpanCornerFarSite, unitVector]

@[simp]
theorem conjSpanCornerFarSite_apply_ne {d : ℕ}
    {a b : Fin d} (hab : b ≠ a) (t : ℕ) :
    conjSpanCornerFarSite a t b = 0 := by
  simp [conjSpanCornerFarSite, unitVector, hab]

@[simp]
theorem conjSpanCornerUpperLeftSite_apply_arm {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    conjSpanCornerUpperLeftSite a b s t a = -(s : ℤ) := by
  simp [conjSpanCornerUpperLeftSite, conjSpanCornerOriginSite,
    Lattice.Cubic.translate, unitVector, hab]

@[simp]
theorem conjSpanCornerUpperLeftSite_apply_transverse {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    conjSpanCornerUpperLeftSite a b s t b = s + t := by
  simp [conjSpanCornerUpperLeftSite, conjSpanCornerOriginSite,
    Lattice.Cubic.translate, unitVector, hab.symm]

@[simp]
theorem conjSpanCornerUpperLeftSite_apply_other {d : ℕ}
    {a b i : Fin d} (hia : i ≠ a) (hib : i ≠ b) (s t : ℕ) :
    conjSpanCornerUpperLeftSite a b s t i = 0 := by
  simp [conjSpanCornerUpperLeftSite, conjSpanCornerOriginSite,
    Lattice.Cubic.translate, unitVector, hia, hib]

/-- The straight arm from `t e_a` back to `-s e_a`. -/
def conjSpanCornerArmToOrigin (a : Fin d) (s t : ℕ) :
    Lattice.Cubic.Path (conjSpanCornerFarSite a t)
      (conjSpanCornerOriginSite a s) :=
  YangMills.Basic.OrientedPath.castTarget
    (Path.straight (conjSpanCornerFarSite a t) (.backward a) (s + t)) (by
      rw [Path.advance_eq]
      ext i
      by_cases hi : i = a
      · subst i
        simp [conjSpanCornerFarSite, conjSpanCornerOriginSite,
          SignedDirection.delta_backward, unitVector]
      · simp [conjSpanCornerFarSite, conjSpanCornerOriginSite,
          SignedDirection.delta_backward, unitVector, hi])

/-- The affine straight arm stays on the positive side of the bending
diagonal `x_a-x_b=-s`. -/
theorem conjSpanCornerArmToOrigin_supportedInDiagonalPositiveHalf
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    Endpoint.Path.SupportedInDiagonalPositiveHalf a b (-(s : ℤ))
      (conjSpanCornerArmToOrigin a s t) := by
  intro e he
  unfold conjSpanCornerArmToOrigin at he
  rw [Path.edgeSupport_castTarget] at he
  have ha := straight_backward_edgeSupport_coordinate_bounds
    (conjSpanCornerFarSite a t) a (s + t) e he
  have hb := straight_edgeSupport_coordinate_eq
    (conjSpanCornerFarSite a t) (.backward a) (s + t) b hab e he
  rw [conjSpanCornerFarSite_apply_self] at ha
  rw [conjSpanCornerFarSite_apply_ne hab.symm t] at hb
  omega

/-- The left endpoint is fixed by the bending diagonal. -/
@[simp]
theorem diagonalReflection_conjSpanCornerOriginSite_fixed
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (s : ℕ) :
    diagonalReflection a b (-(s : ℤ))
        (conjSpanCornerOriginSite a s) =
      conjSpanCornerOriginSite a s := by
  ext i
  by_cases hia : i = a
  · subst i
    rw [diagonalReflection_apply_first,
      conjSpanCornerOriginSite_apply_ne hab.symm,
      conjSpanCornerOriginSite_apply_self]
    ring
  · by_cases hib : i = b
    · subst i
      rw [diagonalReflection_apply_second hab,
        conjSpanCornerOriginSite_apply_self,
        conjSpanCornerOriginSite_apply_ne hab.symm]
      ring
    · rw [diagonalReflection_apply_other hia hib]

/-- Bending sends the right endpoint to the upper-left square vertex. -/
theorem diagonalReflection_conjSpanCornerFarSite_eq_upperLeft
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    diagonalReflection a b (-(s : ℤ))
        (conjSpanCornerFarSite a t) =
      conjSpanCornerUpperLeftSite a b s t := by
  ext i
  by_cases hia : i = a
  · subst i
    rw [diagonalReflection_apply_first,
      conjSpanCornerFarSite_apply_ne hab.symm,
      conjSpanCornerUpperLeftSite_apply_arm hab]
    ring
  · by_cases hib : i = b
    · subst i
      rw [diagonalReflection_apply_second hab,
        conjSpanCornerFarSite_apply_self,
        conjSpanCornerUpperLeftSite_apply_transverse hab]
      omega
    · rw [diagonalReflection_apply_other hia hib]
      rw [conjSpanCornerFarSite_apply_ne hia,
        conjSpanCornerUpperLeftSite_apply_other hia hib]

/-- The lower L produced by the first reflection. -/
def conjSpanCornerLowerLPath {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    Lattice.Cubic.Path (conjSpanCornerUpperLeftSite a b s t)
      (conjSpanCornerFarSite a t) :=
  let p := conjSpanCornerArmToOrigin a s t
  YangMills.Basic.OrientedPath.castSource
    ((diagonalReflectedPathToFixed hab (-(s : ℤ)) p
      (diagonalReflection_conjSpanCornerOriginSite_fixed hab s)).comp
        p.reverse)
    (diagonalReflection_conjSpanCornerFarSite_eq_upperLeft hab s t)

/-- The upper L, running from upper-left through upper-right to lower-right. -/
def conjSpanCornerUpperLPath {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    Lattice.Cubic.Path (conjSpanCornerUpperLeftSite a b s t)
      (conjSpanCornerFarSite a t) :=
  let B := conjSpanCornerUpperLeftSite a b s t
  let C := Path.advance B (.forward a) (s + t)
  YangMills.Basic.OrientedPath.castTarget
    ((Path.straight B (.forward a) (s + t)).comp
      (Path.straight C (.backward b) (s + t))) (by
        rw [Path.advance_eq]
        ext i
        by_cases hia : i = a
        · subst i
          simp [B, C, conjSpanCornerUpperLeftSite,
            conjSpanCornerOriginSite, conjSpanCornerFarSite,
            Lattice.Cubic.translate, Path.advance_eq,
            SignedDirection.delta_forward, unitVector, hab]
        · by_cases hib : i = b
          · subst i
            simp [B, C, conjSpanCornerUpperLeftSite,
              conjSpanCornerOriginSite,
              conjSpanCornerFarSite, Lattice.Cubic.translate, unitVector,
              Path.advance_eq, SignedDirection.delta_forward,
              hab, hab.symm]
          · simp [B, C, conjSpanCornerUpperLeftSite,
              conjSpanCornerOriginSite,
              conjSpanCornerFarSite, Lattice.Cubic.translate, unitVector,
              Path.advance_eq, SignedDirection.delta_forward, hia, hib])

/-- Both endpoints of the upper L lie on the closing anti-diagonal. -/
theorem antiDiagonalReflection_conjSpanCornerFarSite_fixed
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    antiDiagonalReflection a b t (conjSpanCornerFarSite a t) =
      conjSpanCornerFarSite a t := by
  ext i
  by_cases hia : i = a
  · subst i
    rw [antiDiagonalReflection_apply_first hab,
      conjSpanCornerFarSite_apply_ne hab.symm,
      conjSpanCornerFarSite_apply_self]
    ring
  · by_cases hib : i = b
    · subst i
      rw [antiDiagonalReflection_apply_second hab,
        conjSpanCornerFarSite_apply_self,
        conjSpanCornerFarSite_apply_ne hab.symm]
      ring
    · simp [antiDiagonalReflection, diagonalReflection, siteReflection,
        conjSpanCornerFarSite, unitVector, hia, hib]

theorem antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    antiDiagonalReflection a b t
        (conjSpanCornerUpperLeftSite a b s t) =
      conjSpanCornerUpperLeftSite a b s t := by
  ext i
  by_cases hia : i = a
  · subst i
    rw [antiDiagonalReflection_apply_first hab,
      conjSpanCornerUpperLeftSite_apply_transverse hab,
      conjSpanCornerUpperLeftSite_apply_arm hab]
    omega
  · by_cases hib : i = b
    · subst i
      rw [antiDiagonalReflection_apply_second hab,
        conjSpanCornerUpperLeftSite_apply_arm hab,
        conjSpanCornerUpperLeftSite_apply_transverse hab]
      omega
    · simp [antiDiagonalReflection, diagonalReflection, siteReflection,
        conjSpanCornerUpperLeftSite_apply_other hia hib, hia, hib]

/-- The upper L lies in the positive half of `x_a+x_b=t`. -/
theorem conjSpanCornerUpperLPath_supportedInAntiDiagonalPositiveHalf
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    Endpoint.Path.SupportedInAntiDiagonalPositiveHalf a b t
      (conjSpanCornerUpperLPath hab s t) := by
  intro e he
  unfold conjSpanCornerUpperLPath at he
  rw [Path.edgeSupport_castTarget, Path.edgeSupport_comp] at he
  let B := conjSpanCornerUpperLeftSite a b s t
  let C := Path.advance B (.forward a) (s + t)
  have hBa : B a = -(s : ℤ) := by
    exact conjSpanCornerUpperLeftSite_apply_arm hab s t
  have hBb : B b = s + t := by
    exact conjSpanCornerUpperLeftSite_apply_transverse hab s t
  have hCa : C a = t := by
    simp [C, Path.advance_eq, hBa, SignedDirection.delta_forward,
      unitVector]
  have hCb : C b = s + t := by
    simp [C, Path.advance_eq, hBb, SignedDirection.delta_forward,
      unitVector, hab.symm]
  rcases Finset.mem_union.mp he with he | he
  · have ha := straight_forward_edgeSupport_coordinate_bounds B a (s + t) e he
    have hb := straight_edgeSupport_coordinate_eq
      B (.forward a) (s + t) b hab e he
    rw [hBa] at ha
    rw [hBb] at hb
    omega
  · have hb := straight_backward_edgeSupport_coordinate_bounds C b (s + t) e he
    have ha := straight_edgeSupport_coordinate_eq
      C (.backward b) (s + t) a hab.symm e he
    rw [hCb] at hb
    rw [hCa] at ha
    omega

/-! ## Direction identities and the square closure -/

@[simp]
theorem directions_diagonalReflect_conjSpanCorner
    {x y : Site d} {a b : Fin d} (hab : a ≠ b) (k : ℤ)
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
      rw [Path.directions_cons, ih, Path.directions_cons,
        List.map_append, List.map_singleton]
      rfl

@[simp]
theorem directions_siteReflect_conjSpanCorner
    {x y : Site d} (a : Fin d) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.siteReflect a k).directions =
      p.directions.map (SignedDirection.siteReflect a) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Path.directions ((siteReflectionPrefunctor a k).mapPath p) = _ at ih
      change Path.directions (((siteReflectionPrefunctor a k).mapPath p).cons
        ((siteReflectionPrefunctor a k).map e)) = _
      rw [Path.directions_cons, ih, Path.directions_cons,
        List.map_append, List.map_singleton]
      rfl

@[simp]
theorem directions_antiDiagonalReflect_conjSpanCorner
    {x y : Site d} {a b : Fin d} (hab : a ≠ b) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.antiDiagonalReflect hab k).directions =
      ((p.directions.map (SignedDirection.siteReflect b)).map
        (SignedDirection.diagonalReflect a b)).map
          (SignedDirection.siteReflect b) := by
  unfold Path.antiDiagonalReflect
  calc
    Path.directions
        ((Path.diagonalReflect a b hab k (Path.siteReflect b 0 p)).siteReflect
          b 0) =
      (Path.directions
        (Path.diagonalReflect a b hab k (Path.siteReflect b 0 p))).map
          (SignedDirection.siteReflect b) :=
      directions_siteReflect_conjSpanCorner b 0 _
    _ = ((Path.directions (Path.siteReflect b 0 p)).map
          (SignedDirection.diagonalReflect a b)).map
          (SignedDirection.siteReflect b) := by
      rw [directions_diagonalReflect_conjSpanCorner]
    _ = ((p.directions.map (SignedDirection.siteReflect b)).map
          (SignedDirection.diagonalReflect a b)).map
          (SignedDirection.siteReflect b) := by
      rw [directions_siteReflect_conjSpanCorner]

@[simp]
theorem directions_conjSpanCornerArmToOrigin
    (a : Fin d) (s t : ℕ) :
    (conjSpanCornerArmToOrigin a s t).directions =
      List.replicate (s + t) (.backward a) := by
  simp [conjSpanCornerArmToOrigin]

@[simp]
theorem directions_conjSpanCornerUpperLPath
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    (conjSpanCornerUpperLPath hab s t).directions =
      List.replicate (s + t) (.forward a) ++
        List.replicate (s + t) (.backward b) := by
  simp [conjSpanCornerUpperLPath]

@[simp]
theorem diagonalReflect_backward_left_conjSpanCorner
    {a b : Fin d} (hab : a ≠ b) :
    SignedDirection.diagonalReflect a b (.backward a) = .backward b := by
  simp [SignedDirection.diagonalReflect, SignedDirection.backward, hab]

@[simp]
theorem antiDiagonalDirection_forward_left_conjSpanCorner
    {a b : Fin d} (hab : a ≠ b) :
    SignedDirection.siteReflect b
      (SignedDirection.diagonalReflect a b
        (SignedDirection.siteReflect b (.forward a))) = .backward b := by
  simp [SignedDirection.siteReflect, SignedDirection.diagonalReflect,
    SignedDirection.forward, SignedDirection.backward, hab]

@[simp]
theorem antiDiagonalDirection_backward_right_conjSpanCorner
    {a b : Fin d} (hab : a ≠ b) :
    SignedDirection.siteReflect b
      (SignedDirection.diagonalReflect a b
        (SignedDirection.siteReflect b (.backward b))) = .forward a := by
  simp [SignedDirection.siteReflect, SignedDirection.diagonalReflect,
    SignedDirection.forward, SignedDirection.backward, hab]

@[simp]
theorem reverse_backward_direction_conjSpanCorner (a : Fin d) :
    (SignedDirection.backward a).reverse = .forward a :=
  rfl

@[simp]
theorem directions_conjSpanCornerLowerLPath
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    (conjSpanCornerLowerLPath hab s t).directions =
      List.replicate (s + t) (.backward b) ++
        List.replicate (s + t) (.forward a) := by
  simp [conjSpanCornerLowerLPath, diagonalReflectedPathToFixed,
    diagonalReflect_backward_left_conjSpanCorner hab,
    List.reverse_replicate]
  right
  rfl

/-- Reflecting the upper L through its closing plane gives the lower L. -/
theorem antiDiagonalReflected_conjSpanCornerUpperLPath_eq_lower
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    antiDiagonalReflectedPathFixed hab t
      (conjSpanCornerUpperLPath hab s t)
      (antiDiagonalReflection_conjSpanCornerUpperLeftSite_fixed hab s t)
      (antiDiagonalReflection_conjSpanCornerFarSite_fixed hab s t) =
        conjSpanCornerLowerLPath hab s t := by
  apply Path.ext_directions
  simp [antiDiagonalReflectedPathFixed, hab, List.map_map,
    Function.comp_def]

/-- The translated square loop, based at the right endpoint. -/
def conjSpanCornerSquareLoop {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    Lattice.Cubic.Path (conjSpanCornerFarSite a t)
      (conjSpanCornerFarSite a t) :=
  (conjSpanCornerLowerLPath hab s t).reverse.comp
    (conjSpanCornerUpperLPath hab s t)

@[simp]
theorem directions_conjSpanCornerSquareLoop
    {a b : Fin d} (hab : a ≠ b) (s t : ℕ) :
    (conjSpanCornerSquareLoop hab s t).directions =
      List.replicate (s + t) (.backward a) ++
      List.replicate (s + t) (.forward b) ++
      List.replicate (s + t) (.forward a) ++
      List.replicate (s + t) (.backward b) := by
  simp [conjSpanCornerSquareLoop, List.reverse_replicate,
    SignedDirection.reverse, SignedDirection.forward,
    SignedDirection.backward, List.append_assoc]

end

end YangMills.Gluelump.Propagation
