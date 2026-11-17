/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Geometry
import GluelumpPerimeterLaw.Endpoint.LoopFamily

/-!
# Explicit independent transverse endpoint loops

For `3 ≤ d`, take nested rectangles in the plane spanned by axes `1` and `2`.
The `i`th rectangle has width `i + 1` and height one.  Its far vertical edge
is used by no other rectangle in the family, while every horizontal edge and
the common vertical edge at the base are fixed to the identity.  This gives a
direct configuration realizing arbitrary prescribed loop holonomies.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

/-- Nested based rectangles in the fixed transverse coordinate plane. -/
def transverseLoop {d m : ℕ} (hd : 3 ≤ d) (x : Site d) (i : Fin m) :
    Lattice.Cubic.Path x x :=
  Path.rectangleBoundary x (Geometry.transverseAxis₁ hd)
    (Geometry.transverseAxis₂ hd) (i.1 + 1) 1

/-- The distinguished far vertical edge of a transverse rectangle. -/
def transverseLoopFarEdge {d m : ℕ} (hd : 3 ≤ d) (x : Site d)
    (i : Fin m) : PositiveEdge d :=
  ⟨Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1),
    Geometry.transverseAxis₂ hd⟩

theorem advance_coordinate_eq_of_axis_ne {d : ℕ} (x : Site d)
    (s : SignedDirection d) (r : ℕ) (a : Fin d) (hsa : s.axis ≠ a) :
    Path.advance x s r a = x a := by
  rw [Path.advance_eq]
  cases s with
  | mk axis orientation =>
      have haxis : axis ≠ a := hsa
      cases orientation <;>
        simp [SignedDirection.delta, unitVector, Ne.symm haxis]

theorem straight_edgeSupport_coordinate_eq {d : ℕ} (x : Site d)
    (s : SignedDirection d) (r : ℕ) (a : Fin d) (hsa : s.axis ≠ a) :
    ∀ e ∈ (Path.straight x s r).edgeSupport,
      e.source a = x a ∧ e.target a = x a := by
  induction r with
  | zero =>
      intro e he
      change e ∈ (∅ : Finset (PositiveEdge d)) at he
      simp at he
  | succ r ihr =>
      intro e he
      simp only [Path.straight, Path.edgeSupport_cons, Finset.mem_insert] at he
      rcases he with rfl | he
      · have hadv := advance_coordinate_eq_of_axis_ne x s r a hsa
        cases s with
        | mk axis orientation =>
            have haxis : axis ≠ a := hsa
            cases orientation with
            | forward =>
                change Path.advance x (.forward axis) r a = x a ∧
                  step (Path.advance x (.forward axis) r) (.forward axis) a = x a
                constructor
                · exact hadv
                · simpa [step, SignedDirection.forward, SignedDirection.delta,
                    unitVector, Ne.symm haxis] using hadv
            | backward =>
                have hstep :
                    step (Path.advance x (.backward axis) r) (.backward axis) a =
                      x a := by
                  simpa [step, SignedDirection.delta, unitVector, haxis,
                    SignedDirection.backward, Ne.symm haxis] using hadv
                change step (Path.advance x (.backward axis) r) (.backward axis) a =
                    x a ∧
                  step (step (Path.advance x (.backward axis) r) (.backward axis))
                    (.forward axis) a = x a
                constructor
                · exact hstep
                · simpa [step, SignedDirection.forward, SignedDirection.backward,
                    SignedDirection.delta, unitVector, Ne.symm haxis] using hstep
      · exact ihr e he

/-- A stored edge on a forward coordinate segment stays between the two
endpoint coordinate levels. -/
theorem straight_forward_edgeSupport_coordinate_bounds {d : ℕ}
    (x : Site d) (a : Fin d) : ∀ r : ℕ,
    ∀ e ∈ (Path.straight x (.forward a) r).edgeSupport,
      x a ≤ e.source a ∧ e.source a ≤ x a + r ∧
      x a ≤ e.target a ∧ e.target a ≤ x a + r := by
  intro r
  induction r with
  | zero =>
      intro e he
      change e ∈ (∅ : Finset (PositiveEdge d)) at he
      simp at he
  | succ r ihr =>
      intro e he
      simp only [Path.straight, Path.edgeSupport_cons,
        Finset.mem_insert] at he
      rcases he with rfl | he
      · change x a ≤ Path.advance x (.forward a) r a ∧
          Path.advance x (.forward a) r a ≤ x a + (r + 1) ∧
          x a ≤ step (Path.advance x (.forward a) r) (.forward a) a ∧
          step (Path.advance x (.forward a) r) (.forward a) a ≤
            x a + (r + 1)
        simp [Path.advance_eq, step, SignedDirection.forward,
          SignedDirection.delta, unitVector]
        omega
      · obtain ⟨hs0, hs1, ht0, ht1⟩ := ihr e he
        exact ⟨hs0, by omega, ht0, by omega⟩

/-- A stored edge on a backward coordinate segment stays between the two
endpoint coordinate levels. -/
theorem straight_backward_edgeSupport_coordinate_bounds {d : ℕ}
    (x : Site d) (a : Fin d) : ∀ r : ℕ,
    ∀ e ∈ (Path.straight x (.backward a) r).edgeSupport,
      x a - r ≤ e.source a ∧ e.source a ≤ x a ∧
      x a - r ≤ e.target a ∧ e.target a ≤ x a := by
  intro r
  induction r with
  | zero =>
      intro e he
      change e ∈ (∅ : Finset (PositiveEdge d)) at he
      simp at he
  | succ r ihr =>
      intro e he
      simp only [Path.straight, Path.edgeSupport_cons,
        Finset.mem_insert] at he
      rcases he with rfl | he
      · change x a - (r + 1) ≤
            step (Path.advance x (.backward a) r) (.backward a) a ∧
          step (Path.advance x (.backward a) r) (.backward a) a ≤ x a ∧
          x a - (r + 1) ≤
            step (step (Path.advance x (.backward a) r) (.backward a))
              (.forward a) a ∧
          step (step (Path.advance x (.backward a) r) (.backward a))
              (.forward a) a ≤ x a
        simp [Path.advance_eq, step, SignedDirection.forward,
          SignedDirection.backward, SignedDirection.delta, unitVector]
        omega
      · obtain ⟨hs0, hs1, ht0, ht1⟩ := ihr e he
        exact ⟨by omega, hs1, by omega, ht1⟩

/-- Every stored edge of a transverse loop lies in the coordinate plane of
its base perpendicular to the Wilson-arm axis. -/
theorem transverseLoop_edgeSupport_armPlane {d m : ℕ} (hd : 3 ≤ d)
    (x : Site d) (i : Fin m) :
    ∀ e ∈ (transverseLoop hd x i).edgeSupport,
      e.source (Geometry.armAxis hd) = x (Geometry.armAxis hd) ∧
      e.target (Geometry.armAxis hd) = x (Geometry.armAxis hd) := by
  let a := Geometry.armAxis hd
  let b := Geometry.transverseAxis₁ hd
  let c := Geometry.transverseAxis₂ hd
  let r := i.1 + 1
  have hba : b ≠ a := (Geometry.armAxis_ne_transverseAxis₁ hd).symm
  have hca : c ≠ a := (Geometry.armAxis_ne_transverseAxis₂ hd).symm
  let x₁ := Path.advance x (.forward b) r
  let x₂ := Path.advance x₁ (.forward c) 1
  let x₃ := Path.advance x₂ (.backward b) r
  have hx₁ : x₁ a = x a :=
    advance_coordinate_eq_of_axis_ne x (.forward b) r a hba
  have hx₂ : x₂ a = x a := by
    rw [show x₂ a = x₁ a from
      advance_coordinate_eq_of_axis_ne x₁ (.forward c) 1 a hca, hx₁]
  have hx₃ : x₃ a = x a := by
    rw [show x₃ a = x₂ a from
      advance_coordinate_eq_of_axis_ne x₂ (.backward b) r a hba, hx₂]
  intro e he
  simp only [transverseLoop, Path.rectangleBoundary,
    Path.edgeSupport_castTarget, Path.rectangleRaw, Path.edgeSupport_comp,
    Finset.mem_union] at he
  rcases he with he | he | he | he
  · exact straight_edgeSupport_coordinate_eq x (.forward b) r a hba e he
  · simpa [x₁, hx₁] using
      straight_edgeSupport_coordinate_eq x₁ (.forward c) 1 a hca e he
  · simpa [x₂, hx₂] using
      straight_edgeSupport_coordinate_eq x₂ (.backward b) r a hba e he
  · simpa [x₃, hx₃] using
      straight_edgeSupport_coordinate_eq x₃ (.backward c) 1 a hca e he

/-- The union support of the whole finite transverse loop family stays in the
same arm-perpendicular coordinate plane. -/
theorem basedLoopSupport_transverseLoop_armPlane {d m : ℕ} (hd : 3 ≤ d)
    (x : Site d) :
    ∀ e ∈ basedLoopSupport (transverseLoop (m := m) hd x),
      e.source (Geometry.armAxis hd) = x (Geometry.armAxis hd) ∧
      e.target (Geometry.armAxis hd) = x (Geometry.armAxis hd) := by
  intro e he
  rw [basedLoopSupport, Finset.mem_biUnion] at he
  obtain ⟨i, _hi, hei⟩ := he
  exact transverseLoop_edgeSupport_armPlane hd x i e hei

/-- The first transverse coordinate of every endpoint-collar edge lies
between the base and the width of the largest nested rectangle. -/
theorem basedLoopSupport_transverseLoop_transverseAxis₁_bounds
    {d m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    ∀ e ∈ basedLoopSupport (transverseLoop (m := m) hd x),
      x (Geometry.transverseAxis₁ hd) ≤
          e.source (Geometry.transverseAxis₁ hd) ∧
      e.source (Geometry.transverseAxis₁ hd) ≤
          x (Geometry.transverseAxis₁ hd) + m ∧
      x (Geometry.transverseAxis₁ hd) ≤
          e.target (Geometry.transverseAxis₁ hd) ∧
      e.target (Geometry.transverseAxis₁ hd) ≤
          x (Geometry.transverseAxis₁ hd) + m := by
  intro e he
  rw [basedLoopSupport, Finset.mem_biUnion] at he
  obtain ⟨i, _hi, hei⟩ := he
  let b := Geometry.transverseAxis₁ hd
  let c := Geometry.transverseAxis₂ hd
  let r := i.1 + 1
  let x₁ := Path.advance x (.forward b) r
  let x₂ := Path.advance x₁ (.forward c) 1
  let x₃ := Path.advance x₂ (.backward b) r
  have hrm : r ≤ m := by
    dsimp only [r]
    omega
  have hcb : c ≠ b := (Geometry.transverseAxis₁_ne_transverseAxis₂ hd).symm
  have hx₁ : x₁ b = x b + r := by
    dsimp only [x₁]
    rw [Path.advance_eq]
    simp [SignedDirection.delta_forward, unitVector]
  have hx₂ : x₂ b = x b + r := by
    rw [show x₂ b = x₁ b from
      advance_coordinate_eq_of_axis_ne x₁ (.forward c) 1 b hcb, hx₁]
  have hx₃ : x₃ b = x b := by
    dsimp only [x₃]
    rw [Path.advance_eq]
    simp [SignedDirection.delta_backward, unitVector, hx₂]
  simp only [transverseLoop, Path.rectangleBoundary,
    Path.edgeSupport_castTarget, Path.rectangleRaw, Path.edgeSupport_comp,
    Finset.mem_union] at hei
  change x b ≤ e.source b ∧ e.source b ≤ x b + m ∧
    x b ≤ e.target b ∧ e.target b ≤ x b + m
  rcases hei with hei | hei | hei | hei
  · obtain ⟨hs0, hs1, ht0, ht1⟩ :=
      straight_forward_edgeSupport_coordinate_bounds x b r e hei
    exact ⟨hs0, by omega, ht0, by omega⟩
  · have hconst := straight_edgeSupport_coordinate_eq
      x₁ (.forward c) 1 b hcb e hei
    rw [hx₁] at hconst
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨hs0, hs1, ht0, ht1⟩ :=
      straight_backward_edgeSupport_coordinate_bounds x₂ b r e hei
    rw [hx₂] at hs0 hs1 ht0 ht1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have hconst := straight_edgeSupport_coordinate_eq
      x₃ (.backward c) 1 b hcb e hei
    rw [hx₃] at hconst
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- The short transverse coordinate of every comb edge has width one,
independently of the number of loops. This is the direction used inside the
rectangle plane in the paper's corner argument. -/
theorem basedLoopSupport_transverseLoop_transverseAxis₂_bounds
    {d m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    ∀ e ∈ basedLoopSupport (transverseLoop (m := m) hd x),
      x (Geometry.transverseAxis₂ hd) ≤ e.source (Geometry.transverseAxis₂ hd) ∧
      e.source (Geometry.transverseAxis₂ hd) ≤ x (Geometry.transverseAxis₂ hd) + 1 ∧
      x (Geometry.transverseAxis₂ hd) ≤ e.target (Geometry.transverseAxis₂ hd) ∧
      e.target (Geometry.transverseAxis₂ hd) ≤ x (Geometry.transverseAxis₂ hd) + 1 := by
  intro e he
  rw [basedLoopSupport, Finset.mem_biUnion] at he
  obtain ⟨i, _hi, hei⟩ := he
  let b := Geometry.transverseAxis₁ hd
  let c := Geometry.transverseAxis₂ hd
  let r := i.1 + 1
  let x₁ := Path.advance x (.forward b) r
  let x₂ := Path.advance x₁ (.forward c) 1
  let x₃ := Path.advance x₂ (.backward b) r
  have hbc : b ≠ c := Geometry.transverseAxis₁_ne_transverseAxis₂ hd
  have hx₁ : x₁ c = x c :=
    advance_coordinate_eq_of_axis_ne x (.forward b) r c hbc
  have hx₂ : x₂ c = x c + 1 := by
    dsimp only [x₂]
    rw [Path.advance_eq]
    simp [SignedDirection.delta_forward, unitVector, hx₁]
  have hx₃ : x₃ c = x c + 1 := by
    rw [show x₃ c = x₂ c from
      advance_coordinate_eq_of_axis_ne x₂ (.backward b) r c hbc, hx₂]
  simp only [transverseLoop, Path.rectangleBoundary,
    Path.edgeSupport_castTarget, Path.rectangleRaw, Path.edgeSupport_comp,
    Finset.mem_union] at hei
  change x c ≤ e.source c ∧ e.source c ≤ x c + 1 ∧
    x c ≤ e.target c ∧ e.target c ≤ x c + 1
  rcases hei with hei | hei | hei | hei
  · have hconst := straight_edgeSupport_coordinate_eq x (.forward b) r c hbc e hei
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have hbounds := straight_forward_edgeSupport_coordinate_bounds x₁ c 1 e hei
    rw [hx₁] at hbounds
    exact hbounds
  · have hconst := straight_edgeSupport_coordinate_eq x₂ (.backward b) r c hbc e hei
    rw [hx₂] at hconst
    exact ⟨by omega, by omega, by omega, by omega⟩
  · have hbounds := straight_backward_edgeSupport_coordinate_bounds x₃ c 1 e hei
    rw [hx₃] at hbounds
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem transverseLoopFarEdge_injective {d m : ℕ} (hd : 3 ≤ d)
    (x : Site d) : Function.Injective (transverseLoopFarEdge hd x :
      Fin m → PositiveEdge d) := by
  intro i j hij
  have hs := congrArg (fun e : PositiveEdge d =>
    e.source (Geometry.transverseAxis₁ hd)) hij
  simp only [transverseLoopFarEdge, Path.advance_eq,
    SignedDirection.delta_forward] at hs
  simp [unitVector] at hs
  exact Fin.ext (by omega)

/-- Configuration which places `u i` on the distinguished far edge of the
`i`th loop and the identity on every other stored edge. -/
def transverseLoopConfiguration {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) : Configuration d G :=
  fun e => if he : ∃ i, transverseLoopFarEdge hd x i = e then
    u (Classical.choose he) else 1

@[simp]
theorem transverseLoopConfiguration_farEdge {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) (i : Fin m) :
    transverseLoopConfiguration hd x u (transverseLoopFarEdge hd x i) = u i := by
  rw [transverseLoopConfiguration]
  split_ifs with h
  · have hchosen := Classical.choose_spec h
    have hi : Classical.choose h = i :=
      transverseLoopFarEdge_injective hd x hchosen
    rw [hi]
  · exact False.elim (h ⟨i, rfl⟩)

theorem transverseLoopConfiguration_eq_one_of_direction_ne
    {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) (e : PositiveEdge d)
    (he : e.direction ≠ Geometry.transverseAxis₂ hd) :
    transverseLoopConfiguration hd x u e = 1 := by
  rw [transverseLoopConfiguration]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    apply False.elim
    apply he
    rw [← hi]
    rfl
  · rfl

theorem transverseLoopConfiguration_baseEdge {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) :
    transverseLoopConfiguration hd x u
      ⟨x, Geometry.transverseAxis₂ hd⟩ = 1 := by
  rw [transverseLoopConfiguration]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have hs := congrArg (fun e : PositiveEdge d =>
      e.source (Geometry.transverseAxis₁ hd)) hi
    simp only [transverseLoopFarEdge, Path.advance_eq,
      SignedDirection.delta_forward] at hs
    simp [unitVector] at hs
    omega
  · rfl

private theorem holonomy_straight_transverseAxis₁_eq_one
    {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x₀ x : Site d) (u : Fin m → G)
    (o : Orientation) (r : ℕ) :
    holonomy (transverseLoopConfiguration hd x₀ u)
      (Path.straight x ⟨Geometry.transverseAxis₁ hd, o⟩ r) = 1 := by
  induction r with
  | zero => rfl
  | succ r ihr =>
      rw [Path.straight, holonomy_cons, ihr]
      simp only [one_mul]
      cases o <;>
        simp [signedEdgeValue,
          transverseLoopConfiguration_eq_one_of_direction_ne hd x₀ u,
          Geometry.transverseAxis₁_ne_transverseAxis₂ hd]

/-- Each explicit transverse rectangle has its prescribed holonomy in the
sparse configuration. -/
theorem holonomy_transverseLoopConfiguration_transverseLoop
    {d m : ℕ} {G : Type*} [Group G]
    (hd : 3 ≤ d) (x : Site d) (u : Fin m → G) (i : Fin m) :
    holonomy (transverseLoopConfiguration hd x u) (transverseLoop hd x i) = u i := by
  simp only [transverseLoop, Path.rectangleBoundary, holonomy_castTarget,
    Path.rectangleRaw, holonomy_comp]
  have hbottom : holonomy (transverseLoopConfiguration hd x u)
      (Path.straight x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1)) = 1 := by
    simpa [SignedDirection.forward] using
      holonomy_straight_transverseAxis₁_eq_one
        hd x x u .forward (i.1 + 1)
  rw [hbottom]
  simp only [one_mul]
  rw [show holonomy (transverseLoopConfiguration hd x u)
      (Path.straight
        (Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
        (.forward (Geometry.transverseAxis₂ hd)) 1) = u i by
    simp only [Path.straight, holonomy_cons, holonomy_nil, one_mul,
      Path.advance]
    exact transverseLoopConfiguration_farEdge hd x u i]
  have htop : holonomy (transverseLoopConfiguration hd x u)
      (Path.straight
        (Path.advance
          (Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
          (.forward (Geometry.transverseAxis₂ hd)) 1)
        (.backward (Geometry.transverseAxis₁ hd)) (i.1 + 1)) = 1 := by
    simpa [SignedDirection.backward] using
      holonomy_straight_transverseAxis₁_eq_one hd x
        (Path.advance
          (Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
          (.forward (Geometry.transverseAxis₂ hd)) 1)
        u .backward (i.1 + 1)
  rw [htop]
  simp only [one_mul]
  rw [show holonomy (transverseLoopConfiguration hd x u)
      (Path.straight
        (Path.advance
          (Path.advance
            (Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
            (.forward (Geometry.transverseAxis₂ hd)) 1)
          (.backward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
        (.backward (Geometry.transverseAxis₂ hd)) 1) = 1 by
    have hreturn :
        Path.advance
          (Path.advance
            (Path.advance x (.forward (Geometry.transverseAxis₁ hd)) (i.1 + 1))
            (.forward (Geometry.transverseAxis₂ hd)) 1)
          (.backward (Geometry.transverseAxis₁ hd)) (i.1 + 1) =
          Path.advance x (.forward (Geometry.transverseAxis₂ hd)) 1 := by
      simp only [Path.advance_eq, SignedDirection.delta_forward,
        SignedDirection.delta_backward]
      ext k
      simp [Pi.add_apply]
      ring
    rw [hreturn]
    simp only [Path.straight, Path.advance, holonomy_cons, holonomy_nil, one_mul]
    change (transverseLoopConfiguration hd x u
      ⟨step (step x (.forward (Geometry.transverseAxis₂ hd)))
        (.backward (Geometry.transverseAxis₂ hd)),
        Geometry.transverseAxis₂ hd⟩)⁻¹ = 1
    have hstep : step (step x (.forward (Geometry.transverseAxis₂ hd)))
        (.backward (Geometry.transverseAxis₂ hd)) = x := by
      simpa [SignedDirection.forward, SignedDirection.backward] using
        step_reverse x (.forward (Geometry.transverseAxis₂ hd))
    rw [hstep, transverseLoopConfiguration_baseEdge, inv_one]]
  simp

/-- The nested transverse rectangles allow independent prescribed
holonomies.  This discharges the endpoint nonvanishing geometry predicate. -/
theorem transverseLoop_holonomySurjective
    {d m : ℕ} {G : Type*} [Group G] (hd : 3 ≤ d) (x : Site d) :
    BasedLoopHolonomySurjective (G := G) (transverseLoop (m := m) hd x) := by
  intro u
  exact ⟨transverseLoopConfiguration hd x u,
    holonomy_transverseLoopConfiguration_transverseLoop hd x u⟩

end

end YangMills.Gluelump.Endpoint
