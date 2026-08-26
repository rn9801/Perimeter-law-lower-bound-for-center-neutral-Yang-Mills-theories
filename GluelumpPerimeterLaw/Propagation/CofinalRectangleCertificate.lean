/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.Rectangles

/-!
# Collar-aware rectangle propagation

The direct screened endpoint has a fixed support collar.  Consequently the
two diagonal reflection steps are naturally available only on a cofinal set
of sufficiently long odd squares, rather than at every side length.  This
file packages exactly that weaker interface and connects it to the cofinal
odd-square arithmetic already proved in `Rectangles`.

No measure, lattice-gauge model, thermodynamic limit, or strong-coupling
construction enters this module.  Applications instantiate `line`, `bent`,
and `rectangle` with the real parts of the corresponding expectations.
-/

namespace YangMills.Gluelump.Propagation

/-- The reflection consequences needed after straight-line propagation when
the endpoint geometry has a fixed collar cutoff.

Only odd lengths at least `collarCutoff` must support the diagonal bend and
anti-diagonal close.  The rectangle fields are global because they come from
coordinate reflection and the pointwise character bound, independently of
the screened endpoint collar. -/
structure CofinalRectangleReflectionCertificate
    (collarCutoff : ℕ) (D : ℝ)
    (line bent : ℕ → ℝ) (rectangle : ℕ → ℕ → ℝ) : Prop where
  diagonalBend : ∀ l, collarCutoff ≤ l → Odd l →
    line l ^ 2 ≤ bent l
  antiDiagonalClose : ∀ l, collarCutoff ≤ l → Odd l →
    bent l ^ 2 / D ≤ rectangle l l
  rectangleNonneg : ∀ R T, 0 ≤ rectangle R T
  rectangleLeOne : ∀ R T, rectangle R T ≤ 1
  rectangleSideLogConvex : ∀ R, ReflectionLogConvex (rectangle R)
  rectangleTranspose : ∀ R T, rectangle R T = rectangle T R

/-- A power lower bound for the straight screened line gives the required
square lower bound at every odd side length beyond the collar cutoff. -/
theorem CofinalRectangleReflectionCertificate.square_lower_bound_of_line_rate
    {collarCutoff : ℕ} {D q : ℝ}
    {line bent : ℕ → ℝ} {rectangle : ℕ → ℕ → ℝ}
    (cert : CofinalRectangleReflectionCertificate
      collarCutoff D line bent rectangle)
    (hD : 1 ≤ D) (hq : 0 < q)
    (hline : ∀ l, 0 < l → q ^ l ≤ line l)
    {l : ℕ} (hl : 0 < l) (hcutoff : collarCutoff ≤ l)
    (hlOdd : Odd l) :
    q ^ (4 * l) / D ≤ rectangle l l := by
  have hqPow : 0 ≤ q ^ l := pow_nonneg hq.le l
  have hlineBound : q ^ l ≤ line l := hline l hl
  have hlineSq : (q ^ l) ^ 2 ≤ line l ^ 2 :=
    pow_le_pow_left₀ hqPow hlineBound 2
  have hbend : line l ^ 2 ≤ bent l :=
    cert.diagonalBend l hcutoff hlOdd
  have hfour : ((q ^ l) ^ 2) ^ 2 ≤ bent l ^ 2 := by
    calc
      ((q ^ l) ^ 2) ^ 2 ≤ (line l ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg (q ^ l)) hlineSq 2
      _ ≤ bent l ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg (line l)) hbend 2
  calc
    q ^ (4 * l) / D = ((q ^ l) ^ 2) ^ 2 / D := by
      rw [← pow_mul, ← pow_mul]
      congr 2
      omega
    _ ≤ bent l ^ 2 / D :=
      div_le_div_of_nonneg_right hfour (zero_le_one.trans hD)
    _ ≤ rectangle l l := cert.antiDiagonalClose l hcutoff hlOdd

/-- Collar-aware end-to-end arithmetic.

It is enough to know `q^l ≤ line l` for positive straight lengths and the
two corner inequalities for odd `l ≥ collarCutoff`.  The resulting
perimeter base is weakened by the fixed factor `collarCutoff + 3`; it remains
strictly positive and depends only on the straight-line rate, the
representation dimension, and the endpoint collar. -/
theorem CofinalRectangleReflectionCertificate.perimeter_lower_bound_of_line_rate
    {collarCutoff : ℕ} {D q : ℝ}
    {line bent : ℕ → ℝ} {rectangle : ℕ → ℕ → ℝ}
    (cert : CofinalRectangleReflectionCertificate
      collarCutoff D line bent rectangle)
    (hD : 1 ≤ D) (hq : 0 < q) (hqOne : q ≤ 1)
    (hline : ∀ l, 0 < l → q ^ l ≤ line l)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    (q ^ (2 * (collarCutoff + 3)) / D) ^ (2 * (R + T)) ≤
      rectangle R T := by
  exact rectangle_perimeter_lower_bound_of_cofinal_odd_squares
    collarCutoff hD hq hqOne cert.rectangleNonneg cert.rectangleLeOne
    cert.rectangleSideLogConvex cert.rectangleTranspose
    (fun _ hl hcutoff hlOdd ↦
      cert.square_lower_bound_of_line_rate hD hq hline
        hl hcutoff hlOdd)
    hR hT

end YangMills.Gluelump.Propagation
