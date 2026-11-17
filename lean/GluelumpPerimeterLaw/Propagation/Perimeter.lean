/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.PowerLowerBound
import GluelumpPerimeterLaw.Propagation.Rectangles

/-!
# From a one-link power bound to a perimeter power bound

This file performs the exact numerical assembly between Milestones 3 and 4.
Once reflection propagation supplies `(g beta ^ 2 / D) ^ p ≤ W beta p`
and analyticity supplies `c₀ * beta^r ≤ g beta`, the Wilson observable is
bounded below by a fixed power of `beta` per unit perimeter.
-/

namespace YangMills.Gluelump.Propagation

/-! ## Fixed power bases give exponential perimeter rates -/

/-- A canonical strictly subunit base below any positive power base.  The
fixed cap at `1/2` makes its negative logarithm strictly positive even when
the original base is at least one. -/
noncomputable def cappedPowerBase (B : ℝ) : ℝ := min B (1 / 2)

/-- The positive exponential rate associated with `cappedPowerBase`. -/
noncomputable def powerToExponentialRate (B : ℝ) : ℝ :=
  -Real.log (cappedPowerBase B)

/-- Positivity of the power base makes the canonical exponential rate
strictly positive. -/
theorem powerToExponentialRate_pos {B : ℝ} (hB : 0 < B) :
    0 < powerToExponentialRate B := by
  have hcappedPos : 0 < cappedPowerBase B := by
    exact lt_min hB (by norm_num)
  have hcappedOne : cappedPowerBase B < 1 := by
    exact (min_le_right B (1 / 2)).trans_lt (by norm_num)
  exact neg_pos.mpr (Real.log_neg hcappedPos hcappedOne)

/-- The exponential with the canonical rate lies below the corresponding
natural power of the original positive base. -/
theorem exp_neg_powerToExponentialRate_nat_le_pow
    {B : ℝ} (hB : 0 < B) (p : ℕ) :
    Real.exp (-powerToExponentialRate B * (p : ℝ)) ≤ B ^ p := by
  have hcappedPos : 0 < cappedPowerBase B := by
    exact lt_min hB (by norm_num)
  calc
    Real.exp (-powerToExponentialRate B * (p : ℝ)) =
        Real.exp ((p : ℝ) * Real.log (cappedPowerBase B)) := by
      congr 1
      simp only [powerToExponentialRate]
      ring
    _ = (Real.exp (Real.log (cappedPowerBase B))) ^ p :=
      Real.exp_nat_mul _ p
    _ = cappedPowerBase B ^ p := by rw [Real.exp_log hcappedPos]
    _ ≤ B ^ p := pow_le_pow_left₀ hcappedPos.le
      (min_le_left B (1 / 2)) p

/-- Uniform power-to-exponential conversion for rectangle perimeters.

The chosen rate depends only on `B`, and is quantified before the rectangle
side lengths.  Positivity restrictions on the two sides are passed through
unchanged from the supplied power bound. -/
theorem exists_positive_rate_of_rectangle_perimeter_power
    {B : ℝ} {W : ℕ → ℕ → ℝ}
    (hB : 0 < B)
    (hpower : ∀ {R T : ℕ}, 0 < R → 0 < T →
      B ^ (2 * (R + T)) ≤ W R T) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ {R T : ℕ}, 0 < R → 0 < T →
        Real.exp (-rate * ((2 * (R + T) : ℕ) : ℝ)) ≤ W R T := by
  refine ⟨powerToExponentialRate B, powerToExponentialRate_pos hB,
    fun {R T} hR hT ↦ ?_⟩
  exact (exp_neg_powerToExponentialRate_nat_le_pow
    hB (2 * (R + T))).trans (hpower hR hT)

/-- Combine the local one-link power lower bound with a reflection-propagated
perimeter engine. -/
theorem perimeter_power_lower_bound
    {g : ℝ → ℝ} {W : ℝ → ℕ → ℝ}
    {D c0 beta : ℝ} {r p : ℕ}
    (hD : 0 < D) (hc0 : 0 < c0) (hbeta : 0 ≤ beta)
    (hg0 : 0 ≤ g beta) (hg : c0 * beta ^ r ≤ g beta)
    (hpropagate : (g beta ^ 2 / D) ^ p ≤ W beta p) :
    ((c0 ^ 2 / D) * beta ^ (2 * r)) ^ p ≤ W beta p := by
  have hlocal0 : 0 ≤ c0 * beta ^ r :=
    mul_nonneg hc0.le (pow_nonneg hbeta r)
  have hsq : (c0 * beta ^ r) ^ 2 ≤ g beta ^ 2 :=
    (sq_le_sq₀ hlocal0 hg0).2 hg
  have heq : c0 ^ 2 * beta ^ (2 * r) = (c0 * beta ^ r) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
  have hbase : (c0 ^ 2 / D) * beta ^ (2 * r) ≤ g beta ^ 2 / D := by
    rw [div_mul_eq_mul_div, heq]
    exact div_le_div_of_nonneg_right hsq hD.le
  exact (pow_le_pow_left₀ (by positivity) hbase p).trans hpropagate

/-- Rectangle-indexed form, with the lattice perimeter `2 * (R + T)`. -/
theorem rectangle_perimeter_power_lower_bound
    {g : ℝ → ℝ} {W : ℝ → ℕ → ℕ → ℝ}
    {D c0 beta : ℝ} {r R T : ℕ}
    (hD : 0 < D) (hc0 : 0 < c0) (hbeta : 0 ≤ beta)
    (hg0 : 0 ≤ g beta) (hg : c0 * beta ^ r ≤ g beta)
    (hpropagate :
      (g beta ^ 2 / D) ^ (2 * (R + T)) ≤ W beta R T) :
    ((c0 ^ 2 / D) * beta ^ (2 * r)) ^ (2 * (R + T)) ≤
      W beta R T :=
  perimeter_power_lower_bound
    (W := fun b _p => W b R T) (p := 2 * (R + T))
    hD hc0 hbeta hg0 hg hpropagate

/-- A positive power base on `0 < beta ≤ 1` has the logarithmic exponential
form used in the public Seiler theorem.  The explicit constant is
`|log a| + q`. -/
theorem exp_log_perimeter_le_power
    {a beta : ℝ} {q p : ℕ}
    (ha : 0 < a) (hbeta : 0 < beta) (hbetaOne : beta ≤ 1)
    (hq : 0 < q) :
    Real.exp
        (-((|Real.log a| + (q : ℝ)) *
          (1 + |Real.log beta|)) * (p : ℝ)) ≤
      (a * beta ^ q) ^ p := by
  have hlogBeta : Real.log beta ≤ 0 := Real.log_nonpos hbeta.le hbetaOne
  have habsBeta : |Real.log beta| = -Real.log beta := abs_of_nonpos hlogBeta
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hqPos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hlogA : -|Real.log a| ≤ Real.log a := neg_abs_le _
  have hbetaTerm :
      -((q : ℝ) * |Real.log beta|) = (q : ℝ) * Real.log beta := by
    rw [habsBeta]
    ring
  have hsimple :
      -|Real.log a| - (q : ℝ) * |Real.log beta| ≤
        Real.log a + (q : ℝ) * Real.log beta := by
    exact add_le_add hlogA (le_of_eq hbetaTerm)
  have hextra :
      -((|Real.log a| + (q : ℝ)) * (1 + |Real.log beta|)) ≤
        -|Real.log a| - (q : ℝ) * |Real.log beta| := by
    have hA : 0 ≤ |Real.log a| := abs_nonneg _
    have hB : 0 ≤ |Real.log beta| := abs_nonneg _
    nlinarith [mul_nonneg hA hB]
  have hcore :
      -((|Real.log a| + (q : ℝ)) * (1 + |Real.log beta|)) ≤
        Real.log (a * beta ^ q) := by
    calc
      -((|Real.log a| + (q : ℝ)) * (1 + |Real.log beta|)) ≤
          -|Real.log a| - (q : ℝ) * |Real.log beta| := hextra
      _ ≤ Real.log a + (q : ℝ) * Real.log beta := hsimple
      _ = Real.log (a * beta ^ q) := by
        rw [Real.log_mul (ne_of_gt ha) (pow_ne_zero q (ne_of_gt hbeta)),
          Real.log_pow]
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hbase : 0 < a * beta ^ q := mul_pos ha (pow_pos hbeta q)
  calc
    Real.exp
        (-((|Real.log a| + (q : ℝ)) *
          (1 + |Real.log beta|)) * (p : ℝ)) ≤
        Real.exp ((p : ℝ) * Real.log (a * beta ^ q)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hcore hp0
    _ = (Real.exp (Real.log (a * beta ^ q))) ^ p :=
      Real.exp_nat_mul _ p
    _ = (a * beta ^ q) ^ p := by rw [Real.exp_log hbase]

/-- Full numerical assembly of the roadmap's logarithmic perimeter law for a
coordinate rectangle.  All model-specific work is isolated in the one-link
lower bound `hg` and the reflection propagation inequality `hpropagate`. -/
theorem rectangle_exp_perimeter_lower_bound
    {g : ℝ → ℝ} {W : ℝ → ℕ → ℕ → ℝ}
    {D c0 beta : ℝ} {r R T : ℕ}
    (hD : 0 < D) (hc0 : 0 < c0) (hr : 0 < r)
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1)
    (hg0 : 0 ≤ g beta) (hg : c0 * beta ^ r ≤ g beta)
    (hpropagate :
      (g beta ^ 2 / D) ^ (2 * (R + T)) ≤ W beta R T) :
    Real.exp
        (-((|Real.log (c0 ^ 2 / D)| + ((2 * r : ℕ) : ℝ)) *
          (1 + |Real.log beta|)) * ((2 * (R + T) : ℕ) : ℝ)) ≤
      W beta R T := by
  have ha : 0 < c0 ^ 2 / D := div_pos (sq_pos_of_pos hc0) hD
  have hq : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  exact (exp_log_perimeter_le_power ha hbeta hbetaOne hq).trans
    (rectangle_perimeter_power_lower_bound
      hD hc0 hbeta.le hg0 hg hpropagate)

end YangMills.Gluelump.Propagation
