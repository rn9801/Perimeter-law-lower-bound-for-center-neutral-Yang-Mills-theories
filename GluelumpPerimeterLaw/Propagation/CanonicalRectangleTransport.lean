/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.AxisTransport
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation

/-!
# Transport of canonical rectangle expectations

This file isolates the two neutral symmetries needed after reflection
propagation.  Coordinate-transposition invariance carries the origin-based
rectangle from one ordered pair of distinct axes to any other, and
translation invariance carries it to an arbitrary lattice basepoint.

No finite-volume exhaustion or strong-coupling construction enters here.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The rectangle-specific coordinate-swap callback has exactly the abstract
two-swap consequence required to compare arbitrary ordered axis pairs. -/
theorem RectangleAxisSwapInvariant.axisSwapInvariant
    {mu : ProbabilityMeasure (Configuration d G)}
    {rho : ContinuousUnitaryRepData G n}
    (hswap : RectangleAxisSwapInvariant mu rho) (R T : ℕ) :
    AxisSwapInvariant
      (fun a b => rectangleBoundaryIntegral mu rho a b R T) := by
  intro tau sigma hts a b
  exact (hswap hts a b R T).symm

/-- Any two ordered pairs of distinct axes have the same origin-based
rectangle integral in a coordinate-swap invariant state. -/
theorem rectangleBoundaryIntegral_eq_of_distinct
    {mu : ProbabilityMeasure (Configuration d G)}
    {rho : ContinuousUnitaryRepData G n}
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ a b : Fin d} (h₀ : a₀ ≠ b₀) (hab : a ≠ b)
    (R T : ℕ) :
    rectangleBoundaryIntegral mu rho a₀ b₀ R T =
      rectangleBoundaryIntegral mu rho a b R T := by
  exact (hswap.axisSwapInvariant R T).eq_of_distinct h₀ hab

/-- Translation invariance identifies an origin-based rectangle integral
with the same Wilson rectangle at an arbitrary basepoint. -/
theorem rectangleBoundaryIntegral_eq_integral_rectangleBoundary
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (x₀ : Site d) (a b : Fin d) (R T : ℕ) :
    rectangleBoundaryIntegral mu rho a b R T =
      ∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
        ∂(mu : Measure (Configuration d G)) := by
  have htranslate := hstate.localExpectation_translatePullback x₀
    (rho.wilsonLoop (Path.rectangleBoundary 0 a b R T))
  simpa only [LocalObservable.translatePullback_apply,
    wilsonLoop_rectangleBoundary_translate, rectangleBoundaryIntegral]
    using htranslate.symm

/-- Canonical reflection geometry, coordinate swaps, and translations
identify the propagated rectangle with the public Wilson rectangle. -/
theorem canonicalRectangleIntegral_eq_integral_rectangleBoundary
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (hswap : RectangleAxisSwapInvariant mu rho)
    {a₀ b₀ : Fin d} (h₀ : a₀ ≠ b₀)
    (x₀ : Site d) {a b : Fin d} (hab : a ≠ b) (R T : ℕ) :
    canonicalRectangleIntegral mu rho h₀ R T =
      ∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R T) A
        ∂(mu : Measure (Configuration d G)) := by
  calc
    canonicalRectangleIntegral mu rho h₀ R T =
        rectangleBoundaryIntegral mu rho a₀ b₀ R T :=
      canonicalRectangleIntegral_eq_rectangleBoundaryIntegral
        hstate rho h₀ R T
    _ = rectangleBoundaryIntegral mu rho a b R T :=
      rectangleBoundaryIntegral_eq_of_distinct hswap h₀ hab R T
    _ = _ := rectangleBoundaryIntegral_eq_integral_rectangleBoundary
      hstate rho x₀ a b R T

end

end YangMills.Gluelump.Propagation
