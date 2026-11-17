/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation
import GluelumpPerimeterLaw.Propagation.CofinalRectangleCertificate

/-!
# Assemble canonical rectangle and corner certificates

This small neutral adapter combines the analytic rectangle package with the
two collar-aware corner inequalities.  It keeps the direct endpoint geometry
out of the abstract cofinal-square arithmetic.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory
open Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Add the two endpoint-specific corner inequalities to a canonical
rectangle certificate. -/
theorem CanonicalRectangleExpectationCertificate.toCofinal
    {mu : ProbabilityMeasure (Configuration d G)}
    {rho : ContinuousUnitaryRepData G n}
    {a b : Fin d} {hab : a ≠ b}
    (hrect : CanonicalRectangleExpectationCertificate mu rho hab)
    {collarCutoff : ℕ} {D : ℝ} {line bent : ℕ → ℝ}
    (hbend : ∀ l, collarCutoff ≤ l → Odd l →
      line l ^ 2 ≤ bent l)
    (hclose : ∀ l, collarCutoff ≤ l → Odd l →
      bent l ^ 2 / D ≤ canonicalRectangleExpectation mu rho hab l l) :
    CofinalRectangleReflectionCertificate collarCutoff D line bent
      (canonicalRectangleExpectation mu rho hab) where
  diagonalBend := hbend
  antiDiagonalClose := hclose
  rectangleNonneg := hrect.nonnegative
  rectangleLeOne := hrect.le_one
  rectangleSideLogConvex := hrect.side_logConvex
  rectangleTranspose := hrect.transpose

end

end YangMills.Gluelump.Propagation
