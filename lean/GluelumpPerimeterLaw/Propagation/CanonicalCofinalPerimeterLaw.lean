/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalCofinalRectangle
import GluelumpPerimeterLaw.Propagation.CanonicalRectanglePerimeter

/-!
# Neutral perimeter law from a cofinal rectangle certificate

This is the model-independent public-geometry theorem.  A collar-aware
reflection certificate and a positive straight-line power base imply literal
reality and an exponential perimeter lower bound for every coordinate
rectangle.  The chosen rate is a function only of the numerical certificate
parameters, not of the rectangle geometry.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The explicit power base produced by collar-aware corner propagation. -/
def cofinalRectanglePowerBase (collarCutoff : ℕ) (D q : ℝ) : ℝ :=
  q ^ (2 * (collarCutoff + 3)) / D

/-- Deterministic-rate form of collar-aware reflection propagation.  This
form is what lets an application choose the rate before quantifying over a
family of limiting probability measures. -/
theorem perimeterLaw_of_cofinalRectangleCertificate_fixedRate
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    (hrect : CanonicalRectangleExpectationCertificate mu rho h₀)
    {collarCutoff : ℕ} {D q : ℝ}
    {line bent : ℕ → ℝ}
    (hcert : CofinalRectangleReflectionCertificate
      collarCutoff D line bent
        (canonicalRectangleExpectation mu rho h₀))
    (hD : 1 ≤ D) (hq : 0 < q) (hqOne : q ≤ 1)
    (hline : ∀ l, 0 < l → q ^ l ≤ line l) :
    ∀ (x₀ : Site d) (a b : Fin d) (R T : ℕ),
      a ≠ b → 0 < R → 0 < T →
        (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
            ∂(mu : Measure (Configuration d G))) =
            ((∫ A, rho.wilsonLoop
              (Path.rectangleBoundary x₀ a b R T) A
                ∂(mu : Measure (Configuration d G))).re : ℂ) ∧
          Real.exp (-powerToExponentialRate
              (cofinalRectanglePowerBase collarCutoff D q) *
              ((2 * (R + T) : ℕ) : ℝ)) ≤
            (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
              ∂(mu : Measure (Configuration d G))).re := by
  intro x₀ a b R T hab hR hT
  let B : ℝ := cofinalRectanglePowerBase collarCutoff D q
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hB : 0 < B := div_pos (pow_pos hq _) hDpos
  have hpower : B ^ (2 * (R + T)) ≤
      canonicalRectangleExpectation mu rho h₀ R T := by
    exact hcert.perimeter_lower_bound_of_line_rate
      hD hq hqOne hline hR hT
  constructor
  · exact integral_rectangleBoundary_eq_re_of_canonical
      hstate rho hswap h₀ hrect.reality x₀ hab R T
  · exact rectangleBoundary_exp_lower_bound_of_canonical
      hstate rho hswap h₀ hB
        (fun hR' hT' ↦ hcert.perimeter_lower_bound_of_line_rate
          hD hq hqOne hline hR' hT')
        x₀ hab hR hT

/-- Collar-aware reflection propagation in its final neutral form. -/
theorem perimeterLaw_of_cofinalRectangleCertificate
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    (hrect : CanonicalRectangleExpectationCertificate mu rho h₀)
    {collarCutoff : ℕ} {D q : ℝ}
    {line bent : ℕ → ℝ}
    (hcert : CofinalRectangleReflectionCertificate
      collarCutoff D line bent
        (canonicalRectangleExpectation mu rho h₀))
    (hD : 1 ≤ D) (hq : 0 < q) (hqOne : q ≤ 1)
    (hline : ∀ l, 0 < l → q ^ l ≤ line l) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (x₀ : Site d) (a b : Fin d) (R T : ℕ),
        a ≠ b → 0 < R → 0 < T →
          (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
              ∂(mu : Measure (Configuration d G))) =
              ((∫ A, rho.wilsonLoop
                (Path.rectangleBoundary x₀ a b R T) A
                  ∂(mu : Measure (Configuration d G))).re : ℂ) ∧
            Real.exp (-rate * ((2 * (R + T) : ℕ) : ℝ)) ≤
              (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
                ∂(mu : Measure (Configuration d G))).re := by
  let B : ℝ := cofinalRectanglePowerBase collarCutoff D q
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hB : 0 < B := div_pos (pow_pos hq _) hDpos
  refine ⟨powerToExponentialRate B, powerToExponentialRate_pos hB, ?_⟩
  exact perimeterLaw_of_cofinalRectangleCertificate_fixedRate
    hstate rho hswap h₀ hrect hcert hD hq hqOne hline

end

end YangMills.Gluelump.Propagation
