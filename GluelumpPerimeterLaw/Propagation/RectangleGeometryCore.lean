/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.TransverseLoops
import GluelumpPerimeterLaw.Propagation.CanonicalGeometryBase
import GluelumpPerimeterLaw.Propagation.RectangleReflectionCore

/-!
# Neutral coordinate-cap and rectangle geometry

This file contains the parity-adapted site/link cap paths, their exact support
and direction identities, cyclic recutting to the standard rectangle, and
coordinate-swap covariance.  It contains no Gibbs state, thermodynamic limit,
or strong-coupling construction.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint

noncomputable section

/-- Three sides of a coordinate rectangle, with both endpoints at the same
`a`-coordinate level. -/
def coordinateCap {d : ℕ} (a b : Fin d) (s r T : ℕ) :
    Lattice.Cubic.Path (axisPoint a s) (axisPoint a s + axisPoint b T) :=
  let x₀ := axisPoint a s
  let x₁ := Path.advance x₀ (.forward a) r
  let x₂ := Path.advance x₁ (.forward b) T
  let raw := (Path.straight x₀ (.forward a) r).comp
    ((Path.straight x₁ (.forward b) T).comp
      (Path.straight x₂ (.backward a) r))
  YangMills.Basic.OrientedPath.castTarget raw (by
    dsimp [x₀, x₁, x₂]
    rw [Path.advance_eq, Path.advance_eq, Path.advance_eq]
    simp only [SignedDirection.delta_forward, SignedDirection.delta_backward,
      axisPoint]
    ext i
    by_cases hi : i = a <;> by_cases hj : i = b <;>
      by_cases hab : a = b <;> simp [unitVector, hi, hj, hab] <;> omega)

@[simp]
theorem directions_coordinateCap {d : ℕ} (a b : Fin d) (s r T : ℕ) :
    (coordinateCap a b s r T).directions =
      List.replicate r (.forward a) ++
      List.replicate T (.forward b) ++
      List.replicate r (.backward a) := by
  simp [coordinateCap, List.append_assoc]

/-- Every stored edge of a coordinate cap stays at or beyond its starting
level in the transverse coordinate. -/
theorem coordinateCap_coordinate_lower_bound {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (s r T : ℕ) :
    ∀ e ∈ (coordinateCap a b s r T).edgeSupport,
      (s : ℤ) ≤ e.source a ∧ (s : ℤ) ≤ e.target a := by
  intro e he
  unfold coordinateCap at he
  rw [Path.edgeSupport_castTarget, Path.edgeSupport_comp,
    Path.edgeSupport_comp] at he
  rcases Finset.mem_union.mp he with he | he
  · have hbounds := straight_forward_edgeSupport_coordinate_bounds
      (axisPoint a s) a r e he
    rw [axisPoint_apply_self] at hbounds
    exact ⟨hbounds.1, hbounds.2.2.1⟩
  · rcases Finset.mem_union.mp he with he | he
    · have hconst := straight_edgeSupport_coordinate_eq
        (Path.advance (axisPoint a s) (.forward a) r)
        (.forward b) T a (by simpa using hab.symm) e he
      have hx : Path.advance (axisPoint a s) (.forward a) r a = s + r := by
        simp [Path.advance_eq, axisPoint, SignedDirection.delta_forward,
          unitVector]
      rw [hx] at hconst
      omega
    · have hbounds := straight_backward_edgeSupport_coordinate_bounds
        (Path.advance
          (Path.advance (axisPoint a s) (.forward a) r)
          (.forward b) T) a r e he
      have hx : Path.advance
          (Path.advance (axisPoint a s) (.forward a) r)
          (.forward b) T a = s + r := by
        rw [Path.advance_eq, Path.advance_eq]
        simp [axisPoint, SignedDirection.delta_forward, unitVector, hab]
      rw [hx] at hbounds
      omega

/-- Level-zero caps belong to the site-positive algebra. -/
theorem coordinateCap_sitePositive {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    ∀ e ∈ (coordinateCap a b 0 r T).edgeSupport, 0 ≤ e.source a := by
  intro e he
  exact (coordinateCap_coordinate_lower_bound hab 0 r T e he).1

/-- Level-one caps belong to the link-positive algebra for the plane at
`1/2`. -/
theorem coordinateCap_linkPositive {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    ∀ e ∈ (coordinateCap a b 1 r T).edgeSupport, 0 < e.target a := by
  intro e he
  have h := (coordinateCap_coordinate_lower_bound hab 1 r T e he).2
  omega

/-- Level-zero coordinate cap with endpoints stated in the form used by site
reflection. -/
def siteCoordinateCap {d : ℕ} (a b : Fin d) (r T : ℕ) :
    Lattice.Cubic.Path 0 (axisPoint b T) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (coordinateCap a b 0 r T) (by
        ext i
        simp [axisPoint, unitVector])) (by
      ext i
      simp [axisPoint, unitVector])

@[simp]
theorem directions_siteCoordinateCap {d : ℕ}
    (a b : Fin d) (r T : ℕ) :
    (siteCoordinateCap a b r T).directions =
      List.replicate r (.forward a) ++
      List.replicate T (.forward b) ++
      List.replicate r (.backward a) := by
  simp [siteCoordinateCap]

/-- Level-one coordinate cap with endpoints stated as the positive endpoints
of the two crossing links. -/
def linkCoordinateCap {d : ℕ} (a b : Fin d) (r T : ℕ) :
    Lattice.Cubic.Path (step 0 (.forward a))
      (step (axisPoint b T) (.forward a)) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (coordinateCap a b 1 r T) (by
        ext i
        simp [axisPoint, step, SignedDirection.delta_forward, unitVector])) (by
      ext i
      simp [axisPoint, step, SignedDirection.delta_forward, unitVector,
        add_comm])

@[simp]
theorem directions_linkCoordinateCap {d : ℕ}
    (a b : Fin d) (r T : ℕ) :
    (linkCoordinateCap a b r T).directions =
      List.replicate r (.forward a) ++
      List.replicate T (.forward b) ++
      List.replicate r (.backward a) := by
  simp [linkCoordinateCap]

/-- Specialized site cap support. -/
theorem siteCoordinateCap_sitePositive {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    ∀ e ∈ (siteCoordinateCap a b r T).edgeSupport, 0 ≤ e.source a := by
  intro e he
  unfold siteCoordinateCap at he
  rw [Path.edgeSupport_castTarget, Path.edgeSupport_castSource] at he
  exact coordinateCap_sitePositive hab r T e he

/-- Specialized link cap support. -/
theorem linkCoordinateCap_linkPositive {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    ∀ e ∈ (linkCoordinateCap a b r T).edgeSupport, 0 < e.target a := by
  intro e he
  unfold linkCoordinateCap at he
  rw [Path.edgeSupport_castTarget, Path.edgeSupport_castSource] at he
  exact coordinateCap_linkPositive hab r T e he

@[simp]
theorem siteReflection_axisPoint_other_fixed {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (T : ℕ) :
    siteReflection a 0 (axisPoint b T) = axisPoint b T := by
  ext i
  by_cases hi : i = a
  · subst i
    simp [axisPoint_apply_ne hab T]
  · rw [siteReflection_apply_ne hi]

/-- Site-reflection closure of two level-zero caps. -/
def siteClosedCoordinateCaps {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r s T : ℕ) : Lattice.Cubic.Path (axisPoint b T)
      (axisPoint b T) :=
  (siteReflectedPathFixed a 0 (siteCoordinateCap a b r T)
    (by
      ext i
      by_cases hi : i = a
      · subst i
        simp
      · rw [siteReflection_apply_ne hi])
    (siteReflection_axisPoint_other_fixed hab T)).reverse.comp
      (siteCoordinateCap a b s T)

/-- Link-reflection closure of two level-one caps. -/
def linkClosedCoordinateCaps {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r s T : ℕ) : Lattice.Cubic.Path (axisPoint b T)
      (axisPoint b T) :=
  linkClosedCapsPath a 0 0 (axisPoint b T) rfl
    (axisPoint_apply_ne hab T)
    (linkCoordinateCap a b r T) (linkCoordinateCap a b s T) rfl rfl

@[simp]
theorem directions_linkReflect {d : ℕ} {x y : Site d}
    (a : Fin d) (k : ℤ) (p : Lattice.Cubic.Path x y) :
    (p.linkReflect a k).directions =
      p.directions.map (SignedDirection.siteReflect a) := by
  unfold Path.linkReflect
  calc
    (Path.translate (unitVector a) (p.siteReflect a k)).directions =
        (p.siteReflect a k).directions :=
      Path.directions_translate (unitVector a) (p.siteReflect a k)
    _ = _ := directions_siteReflect a k p

/-- Direction word of an integer-plane cap closure. -/
@[simp]
theorem directions_siteClosedCoordinateCaps {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r s T : ℕ) :
    (siteClosedCoordinateCaps hab r s T).directions =
      List.replicate r (.backward a) ++
      List.replicate T (.backward b) ++
      List.replicate (r + s) (.forward a) ++
      List.replicate T (.forward b) ++
      List.replicate s (.backward a) := by
  simp [siteClosedCoordinateCaps, siteReflectedPathFixed,
    SignedDirection.siteReflect, SignedDirection.forward,
    SignedDirection.backward, hab, Ne.symm hab, List.reverse_replicate,
    List.map_replicate, List.append_assoc]
  rw [List.replicate_add]
  simp only [List.append_assoc]

/-- Direction word of a half-integer-plane cap closure; the two explicit
crossing edges contribute the extra unit of width. -/
@[simp]
theorem directions_linkClosedCoordinateCaps {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r s T : ℕ) :
    (linkClosedCoordinateCaps hab r s T).directions =
      List.replicate r (.backward a) ++
      List.replicate T (.backward b) ++
      List.replicate (r + s + 1) (.forward a) ++
      List.replicate T (.forward b) ++
      List.replicate (s + 1) (.backward a) := by
  simp [linkClosedCoordinateCaps, linkClosedCapsPath,
    reflectedMixedFullPath, reflectedIncomingPath, crossingThenPath,
    linkCoordinateCap, coordinateCap,
    SignedDirection.siteReflect, SignedDirection.forward,
    SignedDirection.backward, hab, Ne.symm hab, List.reverse_replicate,
    List.map_replicate, List.append_assoc]
  rw [show r + s + 1 = r + (s + 1) by omega, List.replicate_add]
  simp [List.replicate_succ, List.append_assoc]
  rw [← List.replicate_succ', ← List.replicate_succ]

/-- A parity-adapted representative of an `R × T` rectangle.  Even widths
are site-reflection norm squares and odd widths are link-reflection norm
squares. -/
def reflectedRectangleLoop {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (R T : ℕ) :
    Lattice.Cubic.Path (axisPoint b T) (axisPoint b T) :=
  if Even R then
    siteClosedCoordinateCaps hab (R / 2) (R / 2) T
  else
    linkClosedCoordinateCaps hab (R / 2) (R / 2) T

@[simp]
theorem reflectedRectangleLoop_even {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r T : ℕ) :
    reflectedRectangleLoop hab (2 * r) T =
      siteClosedCoordinateCaps hab r r T := by
  simp [reflectedRectangleLoop]

@[simp]
theorem reflectedRectangleLoop_odd {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (r T : ℕ) :
    reflectedRectangleLoop hab (2 * r + 1) T =
      linkClosedCoordinateCaps hab r r T := by
  unfold reflectedRectangleLoop
  rw [if_neg (Nat.not_even_two_mul_add_one r)]
  congr <;> omega

/-- The integer-plane mixed closure is exactly the balanced odd-width
representative. -/
theorem siteClosedCoordinateCaps_eq_reflectedRectangleLoop_odd
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    siteClosedCoordinateCaps hab r (r + 1) T =
      reflectedRectangleLoop hab (2 * r + 1) T := by
  rw [reflectedRectangleLoop_odd]
  apply Path.ext_directions
  simp
  omega

/-- Reversing the order of the two adjacent link caps makes their mixed
closure exactly the balanced even-width representative. -/
theorem linkClosedCoordinateCaps_succ_eq_reflectedRectangleLoop_even
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (r T : ℕ) :
    linkClosedCoordinateCaps hab (r + 1) r T =
      reflectedRectangleLoop hab (2 * (r + 1)) T := by
  rw [reflectedRectangleLoop_even]
  apply Path.ext_directions
  simp
  omega

/-- The lower-left corner obtained by cutting the parity-adapted rectangle
after its initial backward-horizontal and backward-vertical runs. -/
def rectangleCutBase {d : ℕ} (a b : Fin d) (R T : ℕ) : Site d :=
  Path.advance
    (Path.advance (axisPoint b T) (.backward a) (R / 2))
    (.backward b) T

/-- The initial segment from the chosen top basepoint to the lower-left
corner of the rectangle. -/
def rectangleInitialCut {d : ℕ} (a b : Fin d) (R T : ℕ) :
    Lattice.Cubic.Path (axisPoint b T) (rectangleCutBase a b R T) :=
  (Path.straight (axisPoint b T) (.backward a) (R / 2)).comp
    (Path.straight
      (Path.advance (axisPoint b T) (.backward a) (R / 2))
      (.backward b) T)

/-- The complementary three runs from the lower-left corner back to the
chosen top basepoint. -/
def rectangleRemainder {d : ℕ} {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    Lattice.Cubic.Path (rectangleCutBase a b R T) (axisPoint b T) :=
  let x₀ := rectangleCutBase a b R T
  let x₁ := Path.advance x₀ (.forward a) R
  let x₂ := Path.advance x₁ (.forward b) T
  let raw := (Path.straight x₀ (.forward a) R).comp
    ((Path.straight x₁ (.forward b) T).comp
      (Path.straight x₂ (.backward a) (R - R / 2)))
  YangMills.Basic.OrientedPath.castTarget raw (by
    dsimp [x₀, x₁, x₂, rectangleCutBase]
    rw [Path.advance_eq, Path.advance_eq, Path.advance_eq,
      Path.advance_eq, Path.advance_eq]
    ext i
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp [axisPoint, SignedDirection.delta_forward,
        SignedDirection.delta_backward, unitVector, hia, hib, hab] <;> omega)

@[simp]
theorem directions_rectangleInitialCut {d : ℕ}
    (a b : Fin d) (R T : ℕ) :
    (rectangleInitialCut a b R T).directions =
      List.replicate (R / 2) (.backward a) ++
        List.replicate T (.backward b) := by
  unfold rectangleInitialCut
  rw [Path.directions_comp, Path.directions_straight]
  congr 1
  exact Path.directions_straight _ _ _

@[simp]
theorem directions_rectangleRemainder {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (R T : ℕ) :
    (rectangleRemainder hab R T).directions =
      List.replicate R (.forward a) ++
        List.replicate T (.forward b) ++
          List.replicate (R - R / 2) (.backward a) := by
  unfold rectangleRemainder
  rw [Path.directions_castTarget, Path.directions_comp,
    Path.directions_comp]
  simp only [Path.directions_straight]
  rw [List.append_assoc]

/-- Uniform direction word for both parity choices of the reflected
rectangle representative. -/
@[simp]
theorem directions_reflectedRectangleLoop {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (R T : ℕ) :
    (reflectedRectangleLoop hab R T).directions =
      List.replicate (R / 2) (.backward a) ++
        List.replicate T (.backward b) ++
          List.replicate R (.forward a) ++
            List.replicate T (.forward b) ++
              List.replicate (R - R / 2) (.backward a) := by
  rcases Nat.even_or_odd' R with ⟨r, rfl | rfl⟩
  · rw [reflectedRectangleLoop_even,
      directions_siteClosedCoordinateCaps]
    have hhalf : 2 * r / 2 = r := by omega
    have hsum : r + r = 2 * r := by omega
    have hback : 2 * r - r = r := by omega
    rw [hhalf, hsum, hback]
  · rw [reflectedRectangleLoop_odd,
      directions_linkClosedCoordinateCaps]
    have hhalf : (2 * r + 1) / 2 = r := by omega
    have hsum : r + r + 1 = 2 * r + 1 := by omega
    have hback : 2 * r + 1 - r = r + 1 := by omega
    rw [hhalf, hsum, hback]

/-- The parity-adapted representative is the initial cut followed by its
three-run complement. -/
theorem reflectedRectangleLoop_eq_cut_comp {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (R T : ℕ) :
    reflectedRectangleLoop hab R T =
      (rectangleInitialCut a b R T).comp (rectangleRemainder hab R T) := by
  apply Path.ext_directions
  simp

/-- Moving the cut to the lower-left corner gives the standard coordinate
rectangle boundary. -/
theorem rectangleRemainder_comp_initialCut {d : ℕ} {a b : Fin d}
    (hab : a ≠ b) (R T : ℕ) :
    (rectangleRemainder hab R T).comp (rectangleInitialCut a b R T) =
      Path.rectangleBoundary (rectangleCutBase a b R T) a b R T := by
  apply Path.ext_directions
  simp only [Path.directions_comp, directions_rectangleRemainder,
    directions_rectangleInitialCut, Path.directions_rectangleBoundary]
  have hback :
      List.replicate (R - R / 2) (SignedDirection.backward a) ++
          List.replicate (R / 2) (SignedDirection.backward a) =
        List.replicate R (SignedDirection.backward a) := by
    rw [← List.replicate_add]
    congr
    omega
  calc
    _ = List.replicate R (.forward a) ++
          List.replicate T (.forward b) ++
            ((List.replicate (R - R / 2) (.backward a) ++
              List.replicate (R / 2) (.backward a)) ++
              List.replicate T (.backward b)) := by
        simp only [List.append_assoc]
    _ = _ := by
      rw [hback]
      simp only [List.append_assoc]

/-- Pointwise cyclic-basepoint identification of the reflected representative
with the standard rectangle boundary. -/
theorem wilsonLoop_reflectedRectangleLoop_eq_rectangleBoundary
    {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) (A : Configuration d G) :
    rho.wilsonLoop (reflectedRectangleLoop hab R T) A =
      rho.wilsonLoop
        (Path.rectangleBoundary (rectangleCutBase a b R T) a b R T) A := by
  rw [reflectedRectangleLoop_eq_cut_comp]
  rw [rho.wilsonLoop_comp_comm]
  rw [rectangleRemainder_comp_initialCut]

/-- The translate of an origin-based rectangle, recast to the literally equal
translated basepoint. -/
def translatedRectangleBoundaryZero {d : ℕ} (v : Site d)
    (a b : Fin d) (R T : ℕ) :
    Lattice.Cubic.Path v v :=
  YangMills.Basic.OrientedPath.castSource
    (YangMills.Basic.OrientedPath.castTarget
      (Path.translate v (Path.rectangleBoundary 0 a b R T))
      (by simp [Lattice.Cubic.translate]))
    (by simp [Lattice.Cubic.translate])

/-- Translating the origin-based standard rectangle gives the same standard
rectangle at the translated basepoint. -/
theorem translatedRectangleBoundaryZero_eq {d : ℕ} (v : Site d)
    (a b : Fin d) (R T : ℕ) :
    translatedRectangleBoundaryZero v a b R T =
      Path.rectangleBoundary v a b R T := by
  apply Path.ext_directions
  simp [translatedRectangleBoundaryZero]

/-- Wilson-loop covariance for the standard rectangle, stated in the form
used by infinite-volume translation invariance. -/
theorem wilsonLoop_rectangleBoundary_translate
    {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (rho : ContinuousUnitaryRepData G n)
    (v : Site d) (a b : Fin d) (R T : ℕ) (A : Configuration d G) :
    rho.wilsonLoop (Path.rectangleBoundary 0 a b R T)
        (LocalObservable.translateConfiguration v A) =
      rho.wilsonLoop (Path.rectangleBoundary v a b R T) A := by
  rw [ContinuousUnitaryRepData.wilsonLoop_apply,
    ContinuousUnitaryRepData.wilsonLoop_apply]
  unfold LocalObservable.translateConfiguration
  rw [holonomy_translateConfiguration]
  calc
    rho.normalizedCharacter
        (holonomy A (Path.translate v
          (Path.rectangleBoundary 0 a b R T))) =
        rho.normalizedCharacter
          (holonomy A (translatedRectangleBoundaryZero v a b R T)) := by
      simp [translatedRectangleBoundaryZero]
    _ = _ := by rw [translatedRectangleBoundaryZero_eq]

/-- A diagonal reflection of an origin-based loop, recast at its fixed
origin basepoint. -/
@[simp]
theorem rectangleDiagonalReflection_zero_fixed {d : ℕ}
    {tau sigma : Fin d} (hts : tau ≠ sigma) :
    diagonalReflection tau sigma 0 (0 : Site d) = 0 := by
  ext i
  by_cases hit : i = tau
  · subst i
    simp
  · by_cases his : i = sigma
    · subst i
      simp [hts]
    · simp [diagonalReflection, hit, his]

/-- A diagonal coordinate swap of an origin-based loop, recast at its fixed
origin basepoint. -/
def diagonalSwapLoopAtZero {d : ℕ} {tau sigma : Fin d}
    (hts : tau ≠ sigma) (p : Lattice.Cubic.Path (0 : Site d) 0) :
    Lattice.Cubic.Path (0 : Site d) 0 :=
  YangMills.Basic.OrientedPath.castSource
    (YangMills.Basic.OrientedPath.castTarget
      (p.diagonalReflect tau sigma hts 0)
        (rectangleDiagonalReflection_zero_fixed hts))
    (rectangleDiagonalReflection_zero_fixed hts)

@[simp]
theorem directions_diagonalSwapLoopAtZero {d : ℕ}
    {tau sigma : Fin d} (hts : tau ≠ sigma)
    (p : Lattice.Cubic.Path (0 : Site d) 0) :
    (diagonalSwapLoopAtZero hts p).directions =
      p.directions.map (SignedDirection.diagonalReflect tau sigma) := by
  simp [diagonalSwapLoopAtZero]

@[simp]
theorem holonomy_diagonalSwapLoopAtZero
    {d : ℕ} {G : Type*} [Group G] {tau sigma : Fin d}
    (hts : tau ≠ sigma) (p : Lattice.Cubic.Path (0 : Site d) 0)
    (A : Configuration d G) :
    holonomy A (diagonalSwapLoopAtZero hts p) =
      holonomy (diagonalReflectConfiguration tau sigma 0 A) p := by
  unfold diagonalSwapLoopAtZero
  rw [holonomy_castSource, holonomy_castTarget,
    holonomy_diagonalReflectConfiguration_path hts]

/-- A coordinate swap sends an origin-based rectangle to the rectangle with
both direction labels swapped, without changing its side lengths. -/
theorem diagonalReflect_rectangleBoundary {d : ℕ}
    {tau sigma : Fin d} (hts : tau ≠ sigma)
    (a b : Fin d) (R T : ℕ) :
    diagonalSwapLoopAtZero hts (Path.rectangleBoundary 0 a b R T) =
      Path.rectangleBoundary 0 (Equiv.swap tau sigma a)
        (Equiv.swap tau sigma b) R T := by
  apply Path.ext_directions
  have hf (i : Fin d) :
      SignedDirection.diagonalReflect tau sigma (.forward i) =
        .forward (Equiv.swap tau sigma i) := rfl
  have hb (i : Fin d) :
      SignedDirection.diagonalReflect tau sigma (.backward i) =
        .backward (Equiv.swap tau sigma i) := rfl
  simp [hf, hb, List.map_append, List.map_replicate]

/-- Wilson-loop covariance under an arbitrary swap of two coordinate axes. -/
theorem wilsonLoop_rectangleBoundary_diagonalReflectConfiguration_swap
    {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (rho : ContinuousUnitaryRepData G n)
    {tau sigma : Fin d} (hts : tau ≠ sigma)
    (a b : Fin d) (R T : ℕ) (A : Configuration d G) :
    rho.wilsonLoop
        (Path.rectangleBoundary 0 (Equiv.swap tau sigma a)
          (Equiv.swap tau sigma b) R T) A =
      rho.wilsonLoop (Path.rectangleBoundary 0 a b R T)
        (diagonalReflectConfiguration tau sigma 0 A) := by
  rw [← diagonalReflect_rectangleBoundary hts]
  simp only [ContinuousUnitaryRepData.wilsonLoop_apply,
    holonomy_diagonalSwapLoopAtZero]

/-- Exchanging the two directed sides and their lengths reverses the
orientation of the same origin-based rectangle. -/
theorem rectangleBoundary_swap_axes_eq_reverse {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    Path.rectangleBoundary 0 b a T R =
      (Path.rectangleBoundary 0 a b R T).reverse := by
  apply Path.ext_directions
  simp [Path.directions_reverse, SignedDirection.reverse,
    SignedDirection.forward, SignedDirection.backward,
    List.reverse_append, List.reverse_replicate, List.append_assoc]

def diagonalReflectedLoopAtZero {d : ℕ} {a b : Fin d} (hab : a ≠ b)
    (p : Lattice.Cubic.Path (0 : Site d) 0) :
    Lattice.Cubic.Path (0 : Site d) 0 :=
  YangMills.Basic.OrientedPath.castSource
    (YangMills.Basic.OrientedPath.castTarget
      (p.diagonalReflect a b hab 0)
        (rectangleDiagonalReflection_zero_fixed hab))
    (rectangleDiagonalReflection_zero_fixed hab)

@[simp]
theorem directions_diagonalReflectedLoopAtZero {d : ℕ}
    {a b : Fin d} (hab : a ≠ b) (p : Lattice.Cubic.Path (0 : Site d) 0) :
    (diagonalReflectedLoopAtZero hab p).directions =
      p.directions.map (SignedDirection.diagonalReflect a b) := by
  simp [diagonalReflectedLoopAtZero]

@[simp]
theorem holonomy_diagonalReflectedLoopAtZero
    {d : ℕ} {G : Type*} [Group G] {a b : Fin d} (hab : a ≠ b)
    (p : Lattice.Cubic.Path (0 : Site d) 0) (A : Configuration d G) :
    holonomy A (diagonalReflectedLoopAtZero hab p) =
      holonomy (diagonalReflectConfiguration a b 0 A) p := by
  unfold diagonalReflectedLoopAtZero
  rw [holonomy_castSource, holonomy_castTarget,
    holonomy_diagonalReflectConfiguration_path hab]

/-- Swapping the two coordinate axes reverses the orientation of the
transposed standard rectangle. -/
theorem diagonalReflectedLoopAtZero_rectangleBoundary
    {d : ℕ} {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    diagonalReflectedLoopAtZero hab
        (Path.rectangleBoundary 0 a b T R) =
      (Path.rectangleBoundary 0 a b R T).reverse := by
  change diagonalSwapLoopAtZero hab
      (Path.rectangleBoundary 0 a b T R) = _
  rw [diagonalReflect_rectangleBoundary hab]
  simpa [hab] using rectangleBoundary_swap_axes_eq_reverse hab R T

/-- Pointwise, evaluating the transposed standard rectangle on the
coordinate-swapped configuration conjugates the original rectangle. -/
theorem wilsonLoop_rectangleBoundary_diagonalReflectConfiguration
    {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (rho : ContinuousUnitaryRepData G n)
    {a b : Fin d} (hab : a ≠ b) (R T : ℕ) (A : Configuration d G) :
    rho.wilsonLoop (Path.rectangleBoundary 0 a b T R)
        (diagonalReflectConfiguration a b 0 A) =
      star (rho.wilsonLoop (Path.rectangleBoundary 0 a b R T) A) := by
  rw [ContinuousUnitaryRepData.wilsonLoop_apply,
    ← holonomy_diagonalReflectedLoopAtZero hab,
    diagonalReflectedLoopAtZero_rectangleBoundary]
  exact rho.wilsonLoop_reverse (Path.rectangleBoundary 0 a b R T) A


end

end YangMills.Gluelump.Propagation
