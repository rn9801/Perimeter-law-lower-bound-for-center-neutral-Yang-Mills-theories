/-
Copyright (c) 2026 The Gluelump Perimeter Law Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Gluelump Perimeter Law contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Coupling-uniform exponential estimates

These numerical lemmas keep the constant outside the positive-coupling
quantifier. They turn a fixed monomial times an exponential into the
`1 + beta + |log beta|` dependence used in the paper.
-/

namespace YangMills.Gluelump.Propagation

noncomputable section

/-- The coupling dependence in the paper's perimeter rate. -/
def couplingWeight (beta : ℝ) : ℝ := 1 + beta + |Real.log beta|

theorem one_le_couplingWeight {beta : ℝ} (hbeta : 0 ≤ beta) :
    1 ≤ couplingWeight beta := by
  unfold couplingWeight
  linarith [abs_nonneg (Real.log beta)]

/-- A coupling-independent coefficient for a monomial-exponential bound. -/
def monomialCouplingConstant (A K : ℝ) (N : ℕ) : ℝ :=
  |Real.log A| + N + K + 1

theorem monomialCouplingConstant_pos {A K : ℝ} (hK : 0 ≤ K) (N : ℕ) :
    0 < monomialCouplingConstant A K N := by
  unfold monomialCouplingConstant
  positivity

/-- An explicit monomial-exponential seed has the paper's coupling weight,
with one coefficient valid at every positive coupling. -/
theorem exp_neg_couplingWeight_le_monomial
    {A K beta : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hbeta : 0 < beta) (N : ℕ) :
    Real.exp (-monomialCouplingConstant A K N * couplingWeight beta) ≤
      A * beta ^ N * Real.exp (-K * beta) := by
  let w := couplingWeight beta
  have hw : 1 ≤ w := one_le_couplingWeight hbeta.le
  have hwbeta : beta ≤ w := by
    dsimp [w, couplingWeight]
    linarith [abs_nonneg (Real.log beta)]
  have hwlog : |Real.log beta| ≤ w := by
    dsimp [w, couplingWeight]
    linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hweighted :
      |Real.log A| + (N : ℝ) * |Real.log beta| + K * beta ≤
        monomialCouplingConstant A K N * w := by
    have h₁ := mul_le_mul_of_nonneg_left hw (abs_nonneg (Real.log A))
    have h₂ := mul_le_mul_of_nonneg_left hwlog hN
    have h₃ := mul_le_mul_of_nonneg_left hwbeta hK
    unfold monomialCouplingConstant
    nlinarith
  have hlogBeta := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log beta)) hN
  have hcore :
      -monomialCouplingConstant A K N * w ≤
        Real.log A + (N : ℝ) * Real.log beta - K * beta := by
    linarith [neg_abs_le (Real.log A)]
  calc
    Real.exp (-monomialCouplingConstant A K N * couplingWeight beta) ≤
        Real.exp (Real.log A + (N : ℝ) * Real.log beta - K * beta) :=
      Real.exp_le_exp.mpr hcore
    _ = A * beta ^ N * Real.exp (-K * beta) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
        Real.exp_log hA, Real.exp_nat_mul, Real.exp_log hbeta]
      simp only [neg_mul]

/-- Propagate a coupling-weight seed through a fixed power and a dimension
factor without introducing a coupling-dependent existential constant. -/
theorem exp_neg_couplingWeight_perimeter_le_power
    {C D beta q : ℝ} (hD : 0 < D) (hbeta : 0 ≤ beta)
    (hq : Real.exp (-C * couplingWeight beta) ≤ q) (k p : ℕ) :
    Real.exp (-((k : ℝ) * C + |Real.log D| + 1) *
        couplingWeight beta * (p : ℝ)) ≤ (q ^ k / D) ^ p := by
  let w := couplingWeight beta
  let B := Real.exp (-C * w) ^ k / D
  have hw : 1 ≤ w := one_le_couplingWeight hbeta
  have hB : 0 < B := div_pos (pow_pos (Real.exp_pos _) _) hD
  have hlog : Real.log B = (k : ℝ) * (-C * w) - Real.log D := by
    dsimp [B]
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt (Real.exp_pos _))) hD.ne',
      Real.log_pow, Real.log_exp]
  have hdimension : Real.log D ≤ (|Real.log D| + 1) * w := by
    have h := mul_le_mul_of_nonneg_left hw (abs_nonneg (Real.log D))
    nlinarith [le_abs_self (Real.log D)]
  have hcore : -((k : ℝ) * C + |Real.log D| + 1) * w ≤ Real.log B := by
    rw [hlog]
    nlinarith
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc
    Real.exp (-((k : ℝ) * C + |Real.log D| + 1) *
        couplingWeight beta * (p : ℝ)) ≤
        Real.exp ((p : ℝ) * Real.log B) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm (p : ℝ)] using mul_le_mul_of_nonneg_right hcore hp
    _ = (Real.exp (Real.log B)) ^ p := Real.exp_nat_mul _ _
    _ = B ^ p := by rw [Real.exp_log hB]
    _ ≤ (q ^ k / D) ^ p := by
      apply pow_le_pow_left₀ hB.le
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_pos _).le hq k) hD.le

/-- The paper's last numerical comparison: a square of side `max(R,S)`
costs at most twice the perimeter exponent, while its dimension factor is
absorbed using `2*(R+S) >= 4`. -/
theorem exp_neg_couplingWeight_rectangle_le_square
    {C D beta q : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hbeta : 0 ≤ beta)
    (hq : Real.exp (-C * couplingWeight beta) ≤ q)
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) :
    Real.exp (-(2 * C + |Real.log D| / 4) * couplingWeight beta *
        ((2 * (R + S) : ℕ) : ℝ)) ≤ q ^ (4 * max R S) / D := by
  let w := couplingWeight beta
  let p := 2 * (R + S)
  let B := Real.exp (-C * w) ^ (4 * max R S) / D
  have hw : 1 ≤ w := one_le_couplingWeight hbeta
  have hB : 0 < B := div_pos (pow_pos (Real.exp_pos _) _) hD
  have hlog : Real.log B =
      ((4 * max R S : ℕ) : ℝ) * (-C * w) - Real.log D := by
    dsimp [B]
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt (Real.exp_pos _))) hD.ne',
      Real.log_pow, Real.log_exp]
  have hp : (4 : ℝ) ≤ p := by
    exact_mod_cast (show 4 ≤ p by dsimp [p]; omega)
  have hmax : ((4 * max R S : ℕ) : ℝ) ≤ 2 * (p : ℝ) := by
    exact_mod_cast (show 4 * max R S ≤ 2 * p by dsimp [p]; omega)
  have hline := mul_le_mul_of_nonneg_right hmax
    (mul_nonneg hC (zero_le_one.trans hw))
  have hwp : (4 : ℝ) ≤ w * (p : ℝ) :=
    hp.trans (by simpa using mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg p))
  have hdim := mul_le_mul_of_nonneg_left hwp
    (div_nonneg (abs_nonneg (Real.log D)) (by norm_num : (0 : ℝ) ≤ 4))
  have hcore : -(2 * C + |Real.log D| / 4) * w * (p : ℝ) ≤ Real.log B := by
    rw [hlog]
    nlinarith [le_abs_self (Real.log D)]
  calc
    Real.exp (-(2 * C + |Real.log D| / 4) * couplingWeight beta *
        ((2 * (R + S) : ℕ) : ℝ)) ≤ Real.exp (Real.log B) :=
      Real.exp_le_exp.mpr hcore
    _ = B := Real.exp_log hB
    _ ≤ q ^ (4 * max R S) / D :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_pos _).le hq _) hD.le

end

end YangMills.Gluelump.Propagation
