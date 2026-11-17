/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.StraightLine

/-!
# Abstract bending and square closing

This module packages the arithmetic after the reflection arguments have
supplied their model-specific inequalities. Coordinate reflection gives the
straight-line estimate, the first diagonal reflection bends the line into an
L, and the second diagonal reflection closes the L into a square.
-/

namespace YangMills.Gluelump.Propagation

/-- The model-specific consequences of coordinate reflection positivity that
are needed to extrapolate a square Wilson-loop lower bound to rectangles.
Keeping these four fields together prevents the final perimeter theorem from
silently assuming the rectangle monotonicity mentioned in the paper. -/
structure RectangleReflectionCertificate (W : ℕ → ℕ → ℝ) : Prop where
  positive : ∀ R T, 0 < W R T
  zero_side_le_one : ∀ R, W R 0 ≤ 1
  side_logConvex : ∀ R, ReflectionLogConvex (W R)
  transpose : ∀ R T, W R T = W T R

/-- The lower bound after one diagonal reflection bends a straight screened
line into an L-shaped correlation. -/
theorem first_power_sq_le_bent {g L : ℕ → ℝ}
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) (hbend : ∀ n, g n ^ 2 ≤ L n)
    {n : ℕ} (hn : 0 < n) :
    g 1 ^ (2 * n) ≤ L n := by
  calc
    g 1 ^ (2 * n) = (g 1 ^ n) ^ 2 := by
      rw [mul_comm 2 n, ← pow_mul]
    _ ≤ (g n) ^ 2 := by
      exact pow_le_pow_left₀ (pow_nonneg (hpos 1).le n)
        (first_power_le_of_pos hlog hpos hzero hn) 2
    _ ≤ L n := hbend n

/-- Two diagonal-reflection steps close the screened line into a square. The
result is the roadmap's square bound `D⁻¹ * g₁^(4n)`. -/
theorem first_power_four_le_square {g L W : ℕ → ℝ} {D : ℝ}
    (hD : 0 < D)
    (hlog : ReflectionLogConvex g) (hpos : ∀ n, 0 < g n)
    (hzero : g 0 ≤ 1) (hbend : ∀ n, g n ^ 2 ≤ L n)
    (hclose : ∀ n, L n ^ 2 / D ≤ W n)
    {n : ℕ} (hn : 0 < n) :
    g 1 ^ (4 * n) / D ≤ W n := by
  have hL : 0 ≤ L n := (sq_nonneg (g n)).trans (hbend n)
  have hbent := first_power_sq_le_bent hlog hpos hzero hbend hn
  calc
    g 1 ^ (4 * n) / D = (g 1 ^ (2 * n)) ^ 2 / D := by
      rw [show 4 * n = (2 * n) * 2 by omega, pow_mul]
    _ ≤ L n ^ 2 / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      exact pow_le_pow_left₀ (pow_nonneg (hpos 1).le (2 * n)) hbent 2
    _ ≤ W n := hclose n

/-- Log-convexity of the Wilson rectangle expectation in either side length
extends the sharp square estimate to arbitrary positive rectangles.  The
conclusion is deliberately weakened to the roadmap's uniform
`(g₁² / D)^perimeter` base, which absorbs both the single square-closing
dimension factor and the interpolation powers. -/
theorem rectangle_perimeter_lower_bound_of_square_of_positive_rows
    {W : ℕ → ℕ → ℝ} {g D : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hgOne : g ≤ 1)
    (hpos : ∀ R, 0 < R → ∀ T, 0 < W R T)
    (hzero : ∀ R, W R 0 ≤ 1)
    (hlog : ∀ R, ReflectionLogConvex (W R))
    (hsymm : ∀ R T, W R T = W T R)
    (hsquare : ∀ n, 0 < n → g ^ (4 * n) / D ≤ W n n)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (g ^ 2 / D) ^ (2 * (R + T)) ≤ W R T := by
  let a := g ^ 2 / D
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have ha : 0 < a := div_pos (sq_pos_of_pos hg) hDpos
  have haOne : a ≤ 1 := by
    calc
      a ≤ g ^ 2 := div_le_self (sq_nonneg g) hD
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ hg.le hgOne 2
      _ = 1 := one_pow 2
  have hsquareWeak (n : ℕ) (hn : 0 < n) :
      a ^ (2 * n) ≤ W n n := by
    have hDpow : D ≤ D ^ (2 * n) := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hD (show 1 ≤ 2 * n by omega))
    have hweak : a ^ (2 * n) ≤ g ^ (4 * n) / D := by
      dsimp [a]
      rw [div_pow, ← pow_mul]
      have hdiv := div_le_div_of_nonneg_left
        (pow_nonneg hg.le (4 * n)) hDpos hDpow
      simpa [show 2 * (2 * n) = 4 * n by omega] using hdiv
    exact hweak.trans (hsquare n hn)
  have main {r t : ℕ} (hr : 0 < r) (hrt : r ≤ t) :
      a ^ (2 * (r + t)) ≤ W r t := by
    have hposr : ∀ u, 0 < W r u := hpos r hr
    have hchord : W r r ^ t ≤ W r t ^ r :=
      pow_le_pow_of_reflectionLogConvex (hlog r) hposr (hzero r) hrt
    have hsquarePow : (a ^ (2 * r)) ^ t ≤ W r r ^ t :=
      pow_le_pow_left₀ (pow_nonneg ha.le (2 * r)) (hsquareWeak r hr) t
    have hexp : 2 * r * t ≤ 2 * (r + t) * r := by
      calc
        2 * r * t ≤ 2 * r * (r + t) :=
          Nat.mul_le_mul_left (2 * r) (Nat.le_add_left t r)
        _ = 2 * (r + t) * r := by ring
    have hbasePow :
        (a ^ (2 * (r + t))) ^ r ≤ (a ^ (2 * r)) ^ t := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_of_le_one ha.le haOne hexp
    have hpow : (a ^ (2 * (r + t))) ^ r ≤ W r t ^ r :=
      hbasePow.trans (hsquarePow.trans hchord)
    exact (pow_le_pow_iff_left₀
      (pow_nonneg ha.le (2 * (r + t))) (hposr t).le hr.ne').mp hpow
  rcases le_total R T with hRT | hTR
  · exact main hR hRT
  · rw [hsymm]
    simpa [Nat.add_comm] using main hT hTR

/-- Global strict positivity is a convenient sufficient hypothesis for the
positive-row form of the rectangle extrapolation theorem. -/
theorem rectangle_perimeter_lower_bound_of_square
    {W : ℕ → ℕ → ℝ} {g D : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hgOne : g ≤ 1)
    (hpos : ∀ R T, 0 < W R T)
    (hzero : ∀ R, W R 0 ≤ 1)
    (hlog : ∀ R, ReflectionLogConvex (W R))
    (hsymm : ∀ R T, W R T = W T R)
    (hsquare : ∀ n, 0 < n → g ^ (4 * n) / D ≤ W n n)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (g ^ 2 / D) ^ (2 * (R + T)) ≤ W R T :=
  rectangle_perimeter_lower_bound_of_square_of_positive_rows
    hD hg hgOne (fun r _hr => hpos r) hzero hlog hsymm hsquare hR hT

/-- Nonnegativity, adjacent log-convexity, and the positive square lower
bound already imply every strict-positivity fact used in rectangle
extrapolation.  No separate positivity hypothesis or logarithm-at-zero
convention is needed. -/
theorem rectangle_perimeter_lower_bound_of_square_of_nonneg
    {W : ℕ → ℕ → ℝ} {g D : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hgOne : g ≤ 1)
    (hnonneg : ∀ R T, 0 ≤ W R T)
    (hzero : ∀ R, W R 0 ≤ 1)
    (hlog : ∀ R, ReflectionLogConvex (W R))
    (hsymm : ∀ R T, W R T = W T R)
    (hsquare : ∀ n, 0 < n → g ^ (4 * n) / D ≤ W n n)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (g ^ 2 / D) ^ (2 * (R + T)) ≤ W R T := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hposRows (r : ℕ) (hr : 0 < r) : ∀ t, 0 < W r t := by
    have hdiag : 0 < W r r :=
      (div_pos (pow_pos hg (4 * r)) hDpos).trans_le (hsquare r hr)
    exact positive_of_reflectionLogConvex_of_pos
      (hlog r) (hnonneg r) hr hdiag
  exact rectangle_perimeter_lower_bound_of_square_of_positive_rows
    hD hg hgOne hposRows hzero hlog hsymm hsquare hR hT

/-- Certificate-packaged form of
`rectangle_perimeter_lower_bound_of_square`. -/
theorem RectangleReflectionCertificate.perimeter_lower_bound_of_square
    {W : ℕ → ℕ → ℝ} (hreflect : RectangleReflectionCertificate W)
    {g D : ℝ} (hD : 1 ≤ D) (hg : 0 < g) (hgOne : g ≤ 1)
    (hsquare : ∀ n, 0 < n → g ^ (4 * n) / D ≤ W n n)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (g ^ 2 / D) ^ (2 * (R + T)) ≤ W R T :=
  rectangle_perimeter_lower_bound_of_square hD hg hgOne
    hreflect.positive hreflect.zero_side_le_one hreflect.side_logConvex
    hreflect.transpose hsquare hR hT

/-- It is enough to prove the square estimate on the cofinal odd subsequence
above a fixed collar cutoff.  Positivity propagates from one such square to
every row; the global character bound and log-convexity then make both side
lengths antitone.  Enlarging a target rectangle to an odd square costs only a
cutoff-dependent weakening of the perimeter base. -/
theorem rectangle_perimeter_lower_bound_of_cofinal_odd_squares
    {W : ℕ → ℕ → ℝ} {g D : ℝ} (m : ℕ)
    (hD : 1 ≤ D) (hg : 0 < g) (hgOne : g ≤ 1)
    (hnonneg : ∀ R T, 0 ≤ W R T)
    (hleOne : ∀ R T, W R T ≤ 1)
    (hlog : ∀ R, ReflectionLogConvex (W R))
    (hsymm : ∀ R T, W R T = W T R)
    (hsquare : ∀ q, 0 < q → m ≤ q → Odd q →
      g ^ (4 * q) / D ≤ W q q)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (g ^ (2 * (m + 3)) / D) ^ (2 * (R + T)) ≤ W R T := by
  let q₀ := 2 * m + 1
  have hq₀ : 0 < q₀ := by simp [q₀]
  have hmq₀ : m ≤ q₀ := by omega
  have hoddq₀ : Odd q₀ := ⟨m, by simp [q₀]⟩
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hdiag₀ : 0 < W q₀ q₀ :=
    (div_pos (pow_pos hg (4 * q₀)) hDpos).trans_le
      (hsquare q₀ hq₀ hmq₀ hoddq₀)
  have hrow₀ : ∀ t, 0 < W q₀ t :=
    positive_of_reflectionLogConvex_of_pos
      (hlog q₀) (hnonneg q₀) hq₀ hdiag₀
  have hpos (r : ℕ) : ∀ t, 0 < W r t := by
    have hrq₀ : 0 < W r q₀ := by
      rw [hsymm]
      exact hrow₀ r
    exact positive_of_reflectionLogConvex_of_pos
      (hlog r) (hnonneg r) hq₀ hrq₀
  have hanti (r : ℕ) : Antitone (W r) :=
    antitone_of_reflectionLogConvex_of_le_one
      (hlog r) (hpos r) (hleOne r)
  let q := 2 * (R + T + m) + 1
  have hq : 0 < q := by simp [q]
  have hmq : m ≤ q := by omega
  have hoddq : Odd q := ⟨R + T + m, by simp [q]⟩
  have hRq : R ≤ q := by omega
  have hTq : T ≤ q := by omega
  have hgeom : W q q ≤ W R T := by
    calc
      W q q ≤ W q T := hanti q hTq
      _ = W T q := hsymm q T
      _ ≤ W T R := hanti T hRq
      _ = W R T := hsymm T R
  have hs : 2 ≤ R + T := by omega
  have hmqBound : 2 * m ≤ m * (R + T) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hs
  have hqBound : q ≤ (m + 3) * (R + T) := by
    dsimp [q]
    rw [Nat.add_mul]
    omega
  have hexp : 4 * q ≤ 4 * ((m + 3) * (R + T)) :=
    Nat.mul_le_mul_left 4 hqBound
  have hg0 : 0 ≤ g := hg.le
  have hnum : g ^ (4 * ((m + 3) * (R + T))) ≤ g ^ (4 * q) :=
    pow_le_pow_of_le_one hg0 hgOne hexp
  have hDpow : D ≤ D ^ (2 * (R + T)) := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hD (show 1 ≤ 2 * (R + T) by omega)
  have hweak :
      (g ^ (2 * (m + 3)) / D) ^ (2 * (R + T)) ≤
        g ^ (4 * q) / D := by
    rw [div_pow, ← pow_mul]
    have hdiv := div_le_div₀ (pow_nonneg hg0 _) hnum hDpos hDpow
    simpa [show (2 * (m + 3)) * (2 * (R + T)) =
      4 * ((m + 3) * (R + T)) by ring] using hdiv
  exact hweak.trans ((hsquare q hq hmq hoddq).trans hgeom)

end YangMills.Gluelump.Propagation
