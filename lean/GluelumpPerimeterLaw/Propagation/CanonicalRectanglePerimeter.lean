/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalRectangleTransport
import GluelumpPerimeterLaw.Propagation.Perimeter

/-!
# Public-geometry consequences of a canonical rectangle power bound

This file performs the model-neutral last step after reflection propagation.
A real power lower bound for one canonical ordered coordinate plane is
transported to every basepoint and every ordered pair of distinct axes.  The
same theorem records literal complex reality and converts the fixed power
base to a strictly positive exponential perimeter rate.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Literal reality of the canonical integral transports to the Wilson
rectangle at every lattice basepoint and in every ordered coordinate plane. -/
theorem integral_rectangleBoundary_eq_re_of_canonical
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    (hreal : ∀ R T, (canonicalRectangleIntegral mu rho h₀ R T).im = 0)
    (x₀ : Site d) {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
        ∂(mu : Measure (Configuration d G))) =
      ((∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
          ∂(mu : Measure (Configuration d G))).re : ℂ) := by
  have hgeom := canonicalRectangleIntegral_eq_integral_rectangleBoundary
    hstate rho hswap h₀ x₀ hab R T
  have him :
      (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
          ∂(mu : Measure (Configuration d G))).im = 0 := by
    rw [← hgeom]
    exact hreal R T
  apply Complex.ext
  · simp
  · simpa only [ContinuousUnitaryRepData.wilsonLoop_apply] using him

/-- A canonical power bound transports without loss to every basepoint and
ordered coordinate plane. -/
theorem rectangleBoundary_power_lower_bound_of_canonical
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    {B : ℝ}
    (hpower : ∀ {R T : ℕ}, 0 < R → 0 < T →
      B ^ (2 * (R + T)) ≤
        canonicalRectangleExpectation mu rho h₀ R T)
    (x₀ : Site d) {a b : Fin d} (hab : a ≠ b)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    B ^ (2 * (R + T)) ≤
      (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
        ∂(mu : Measure (Configuration d G))).re := by
  have hgeom := canonicalRectangleIntegral_eq_integral_rectangleBoundary
    hstate rho hswap h₀ x₀ hab R T
  rw [← hgeom]
  exact hpower hR hT

/-- Public-geometry exponential form.  The displayed rate is determined
solely by `B`, so an application may choose it before quantifying over the
probability measure. -/
theorem rectangleBoundary_exp_lower_bound_of_canonical
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    {B : ℝ} (hB : 0 < B)
    (hpower : ∀ {R T : ℕ}, 0 < R → 0 < T →
      B ^ (2 * (R + T)) ≤
        canonicalRectangleExpectation mu rho h₀ R T)
    (x₀ : Site d) {a b : Fin d} (hab : a ≠ b)
    {R T : ℕ} (hR : 0 < R) (hT : 0 < T) :
    Real.exp (-powerToExponentialRate B *
        ((2 * (R + T) : ℕ) : ℝ)) ≤
      (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
        ∂(mu : Measure (Configuration d G))).re := by
  exact (exp_neg_powerToExponentialRate_nat_le_pow
    hB (2 * (R + T))).trans
      (rectangleBoundary_power_lower_bound_of_canonical
        hstate rho hswap h₀ hpower x₀ hab hR hT)

end

end YangMills.Gluelump.Propagation
