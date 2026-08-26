/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib

/-!
# Abstract transport between ordered coordinate-axis pairs

An isotropic lattice state identifies an observable with its pullback by any
transposition of coordinate axes.  This file isolates the finite combinatorics
needed to pass from one ordered pair of distinct axes to any other: one swap
moves the first axis, and at most one further swap moves the second while
fixing the first.

The result is deliberately independent of lattice paths and measures.  A
geometric application only has to prove the one-swap callback for its
expectation-valued function.
-/

namespace YangMills.Gluelump.Propagation

/-- Invariance of an ordered-axis quantity under simultaneously applying any
nontrivial coordinate transposition to both axes. -/
def AxisSwapInvariant {d : ℕ} {A : Type*}
    (W : Fin d → Fin d → A) : Prop :=
  ∀ (tau sigma : Fin d), tau ≠ sigma → ∀ (a b : Fin d),
    W a b = W (Equiv.swap tau sigma a) (Equiv.swap tau sigma b)

/-- A single coordinate swap can replace the second axis while fixing a
distinct first axis. -/
theorem AxisSwapInvariant.eq_retarget_second
    {d : ℕ} {A : Type*} {W : Fin d → Fin d → A}
    (hW : AxisSwapInvariant W)
    {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) :
    W a b = W a c := by
  by_cases hbc : b = c
  · subst c
    rfl
  · have hswap := hW b c hbc a b
    rw [Equiv.swap_apply_of_ne_of_ne hab hac,
      Equiv.swap_apply_left] at hswap
    exact hswap

/-- Two simultaneous coordinate swaps suffice to carry any ordered pair of
distinct axes to any other ordered pair of distinct axes. -/
theorem AxisSwapInvariant.eq_of_distinct
    {d : ℕ} {A : Type*} {W : Fin d → Fin d → A}
    (hW : AxisSwapInvariant W)
    {a₀ b₀ a b : Fin d} (h₀ : a₀ ≠ b₀) (hab : a ≠ b) :
    W a₀ b₀ = W a b := by
  by_cases ha : a₀ = a
  · subst a
    exact hW.eq_retarget_second h₀ hab
  · let b₁ := Equiv.swap a₀ a b₀
    have hfirst : W a₀ b₀ = W a b₁ := by
      have hswap := hW a₀ a ha a₀ b₀
      simpa only [Equiv.swap_apply_left] using hswap
    have hab₁ : a ≠ b₁ := by
      have hinj := (Equiv.swap a₀ a).injective.ne h₀
      simpa only [Equiv.swap_apply_left] using hinj
    exact hfirst.trans (hW.eq_retarget_second hab₁ hab)

/-- Equality under axis transport preserves literal reality of a complex
expectation, not merely a statement about its real part. -/
theorem AxisSwapInvariant.im_eq_zero_of_distinct
    {d : ℕ} {W : Fin d → Fin d → ℂ}
    (hW : AxisSwapInvariant W)
    {a₀ b₀ a b : Fin d} (h₀ : a₀ ≠ b₀) (hab : a ≠ b)
    (him : Complex.im (W a₀ b₀) = 0) :
    Complex.im (W a b) = 0 := by
  rw [← hW.eq_of_distinct h₀ hab]
  exact him

end YangMills.Gluelump.Propagation
