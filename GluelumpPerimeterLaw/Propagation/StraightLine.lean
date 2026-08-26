/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib

/-!
# Abstract straight-line gluelump propagation

This file isolates the numerical consequence of coordinate reflection
positivity used in Milestone 4. The lattice proof is expected to provide a
strictly positive sequence `g` satisfying the adjacent log-convexity inequality

`g (n + 1) ^ 2 <= g n * g (n + 2)`.

Together with `g 0 <= 1`, this forces `g 1 ^ n <= g n` for every positive
length. No gauge, center, or representation-theory assumption enters this
lemma.
-/

namespace YangMills.Gluelump.Propagation

/-- The adjacent log-convexity inequality produced by reflection
Cauchy--Schwarz for a straight screened line. -/
def ReflectionLogConvex (g : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, g (n + 1) ^ 2 ≤ g n * g (n + 2)

/-- Reflection nonnegativity plus strict positivity at lengths zero and one
propagates strict positivity to every length. Thus later quotient arguments
do not need positivity of the whole sequence as an independent hypothesis. -/
theorem positive_of_reflectionLogConvex {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hnonneg : ∀ n, 0 ≤ g n)
    (hzero : 0 < g 0) (hone : 0 < g 1) : ∀ n, 0 < g n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact hzero
  | one => exact hone
  | more n hn hn1 =>
      have hprod : 0 < g n * g (n + 2) :=
        (sq_pos_of_pos hn1).trans_le (hlog n)
      exact pos_of_mul_pos_right hprod (hnonneg n)

/-- A nonnegative adjacent log-convex sequence that is positive at any
positive index is positive everywhere.  Positivity first propagates
backwards to indices zero and one, after which the usual two-step argument
propagates it forwards. -/
theorem positive_of_reflectionLogConvex_of_pos {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hnonneg : ∀ n, 0 ≤ g n)
    {m : ℕ} (hmIndex : 0 < m) (hm : 0 < g m) : ∀ n, 0 < g n := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hprod : 0 < g m * g (m + 2) :=
        (sq_pos_of_pos hm).trans_le (hlog m)
      have hprev : 0 < g m :=
        pos_of_mul_pos_left hprod (hnonneg (m + 2))
      by_cases hm0 : m = 0
      · subst m
        exact positive_of_reflectionLogConvex hlog hnonneg hprev hm
      · exact ih (Nat.pos_of_ne_zero hm0) hprev

/-- Adjacent log-convexity makes successive quotients monotone. -/
theorem ratio_mono_of_reflectionLogConvex {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n) (n : ℕ) :
    g (n + 1) / g n ≤ g (n + 2) / g (n + 1) := by
  rw [div_le_div_iff₀ (hpos n) (hpos (n + 1))]
  simpa [pow_two, mul_comm] using hlog n

/-- Every successive quotient dominates the first quotient. -/
theorem first_ratio_le_ratio {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n) (n : ℕ) :
    g 1 / g 0 ≤ g (n + 1) / g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ih.trans (ratio_mono_of_reflectionLogConvex hlog hpos n)

/-- If the zero-length norm is at most one, the first screened correlation is
bounded by every successive quotient. -/
theorem first_term_le_ratio {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) (n : ℕ) :
    g 1 ≤ g (n + 1) / g n := by
  have hquotPos : 0 < g 1 / g 0 := div_pos (hpos 1) (hpos 0)
  have hfirst : g 1 ≤ g 1 / g 0 := by
    calc
      g 1 = g 0 * (g 1 / g 0) := by
        field_simp [ne_of_gt (hpos 0)]
      _ ≤ 1 * (g 1 / g 0) :=
        mul_le_mul_of_nonneg_right hzero hquotPos.le
      _ = g 1 / g 0 := one_mul _
  exact hfirst.trans (first_ratio_le_ratio hlog hpos n)

/-- The abstract straight-line propagation bound. Its positive-length form
matches the gluelump roadmap: `g_n >= g_1^n`. -/
theorem first_power_le {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) (n : ℕ) :
    g 1 ^ (n + 1) ≤ g (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hratio := first_term_le_ratio hlog hpos hzero (n + 1)
      have hmul := mul_le_mul ih hratio (hpos 1).le (hpos (n + 1)).le
      calc
        g 1 ^ (n + 1 + 1) = g 1 ^ (n + 1) * g 1 := by rw [pow_succ]
        _ ≤ g (n + 1) * (g (n + 2) / g (n + 1)) := hmul
        _ = g (n + 2) := by
          field_simp [ne_of_gt (hpos (n + 1))]

/-- Equivalent indexing of `first_power_le` for an explicitly positive
length. -/
theorem first_power_le_of_pos {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) {n : ℕ} (hn : 0 < n) :
    g 1 ^ n ≤ g n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact first_power_le hlog hpos hzero m

/-- Straight-line propagation with the hypotheses delivered directly by
reflection positivity: nonnegativity everywhere and strict positivity only
at lengths zero and one. -/
theorem first_power_le_of_reflection_nonneg {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hnonneg : ∀ n, 0 ≤ g n)
    (hzeroPos : 0 < g 0) (honePos : 0 < g 1) (hzero : g 0 ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    g 1 ^ n ≤ g n :=
  first_power_le_of_pos hlog
    (positive_of_reflectionLogConvex hlog hnonneg hzeroPos honePos)
    hzero hn

/-- A positive log-convex sequence lies below every later chord issuing from
the zeroth term.  This is the power form that avoids choosing real roots:
if `r ≤ t`, then `g r ^ t ≤ g t ^ r`. -/
theorem pow_le_pow_of_reflectionLogConvex {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) {r t : ℕ} (hrt : r ≤ t) :
    g r ^ t ≤ g t ^ r := by
  let delta : ℕ → ℝ := fun n => Real.log (g (n + 1)) - Real.log (g n)
  have hdeltaSucc (n : ℕ) : delta n ≤ delta (n + 1) := by
    have hlogIneq := Real.log_le_log (sq_pos_of_pos (hpos (n + 1))) (hlog n)
    rw [Real.log_pow, Real.log_mul (hpos n).ne' (hpos (n + 2)).ne'] at hlogIneq
    dsimp [delta]
    norm_num at hlogIneq ⊢
    linarith
  have hdelta : Monotone delta := monotone_nat_of_le_succ hdeltaSucc
  have hlogZero : Real.log (g 0) ≤ 0 :=
    Real.log_nonpos (hpos 0).le hzero
  have hlogBound : ∀ a b : ℕ, a ≤ b →
      Real.log (g a) ≤ (a : ℝ) * delta b := by
    intro a
    induction a with
    | zero =>
        intro b _hab
        simpa using hlogZero
    | succ a ih =>
        intro b hab
        have hab' : a ≤ b := a.le_succ.trans hab
        have hstep : delta a ≤ delta b := hdelta (Nat.le_of_succ_le hab)
        have hrec := ih b hab'
        dsimp [delta] at hstep hrec ⊢
        rw [Nat.cast_succ]
        linarith
  have hchord : (t : ℝ) * Real.log (g r) ≤
      (r : ℝ) * Real.log (g t) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrt
    induction k with
    | zero => simp
    | succ k ih =>
        have ih' := ih (Nat.le_add_right r k)
        have hbound := hlogBound r (r + k) (Nat.le_add_right r k)
        dsimp [delta] at hbound
        push_cast at ih' hbound ⊢
        rw [show r + (k + 1) = r + k + 1 by omega]
        linarith
  rw [← Real.log_le_log_iff (pow_pos (hpos r) t) (pow_pos (hpos t) r)]
  simpa [Real.log_pow, mul_comm] using hchord

/-- A positive log-convex sequence which is globally bounded above by one is
nonincreasing.  Indeed, if one successive quotient exceeded one, monotonicity
of the quotients would force geometric growth past the global bound. -/
theorem antitone_of_reflectionLogConvex_of_le_one {g : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hone : ∀ n, g n ≤ 1) : Antitone g := by
  intro n k hnk
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
      have hstep : g (k + 1) ≤ g k := by
        by_contra hnot
        have hlt : g k < g (k + 1) := lt_of_not_ge hnot
        let q := g (k + 1) / g k
        have hq : 1 < q := (one_lt_div (hpos k)).2 hlt
        have hratio (j : ℕ) : q ≤ g (k + j + 1) / g (k + j) := by
          induction j with
          | zero => simp [q]
          | succ j ihj =>
              exact ihj.trans (by
                simpa [Nat.add_assoc] using
                  ratio_mono_of_reflectionLogConvex hlog hpos (k + j))
        have hgrowth (j : ℕ) : g k * q ^ j ≤ g (k + j) := by
          induction j with
          | zero => simp
          | succ j ihj =>
              have hmul := mul_le_mul ihj (hratio j)
                (by linarith : 0 ≤ q)
                (hpos (k + j)).le
              calc
                g k * q ^ (j + 1) = (g k * q ^ j) * q := by
                  rw [pow_succ]
                  ring
                _ ≤ g (k + j) * (g (k + j + 1) / g (k + j)) := by
                  simpa [mul_comm] using hmul
                _ = g (k + j + 1) := by
                  field_simp [ne_of_gt (hpos (k + j))]
        obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (g k)⁻¹ hq
        have hgkq : 1 < g k * q ^ j := by
          calc
            1 = g k * (g k)⁻¹ := by
              field_simp [ne_of_gt (hpos k)]
            _ < g k * q ^ j := mul_lt_mul_of_pos_left hj (hpos k)
        exact (hgkq.trans_le ((hgrowth j).trans (hone (k + j)))).false
      exact hstep.trans ih

end YangMills.Gluelump.Propagation
