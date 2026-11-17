/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.CenterScreening
import YangMills.Lattice.Plaquette
import GluelumpPerimeterLaw.Upstream.StrongCoupling.PaperFreeBoundary
import GluelumpPerimeterLaw.Upstream.Wilson.Loop
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The paper's main perimeter-law statement

The headline chooses one constant before the positive coupling, the common
translation-invariant ordinary free-boundary limit, and the rectangle.
`beta` is in the paper's unnormalized-character convention. The finite
Wilson potential is normalized, so its internal coupling is `n * beta`.

The older fixed-coupling qualitative proposition is retained under an
explicitly qualitative name for downstream compatibility.
-/

namespace YangMills.Gluelump.InfiniteVolume

open MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.StrongCoupling
open YangMills.Gluelump.RepresentationTheory

noncomputable section

universe u

/-- The normalized `rho`-Wilson observable around an `R`-by-`T` coordinate
rectangle in the infinite cubic lattice. -/
def rectangleWilsonObservable {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : LocalObservable d G :=
  rho.wilsonLoop (Path.rectangleBoundary x0 a b R T)

/-- Complex expectation of the normalized `rho`-Wilson rectangle in an
infinite-volume probability. -/
def complexRectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℂ :=
  localExpectation mu (rectangleWilsonObservable rho x0 a b R T)

/-- The real coordinate of the complex rectangle expectation.  The main
target includes equality back in `ℂ`, so the lower bound is on the real
expectation itself, not merely on an otherwise complex expectation's real
part. -/
def rectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℝ :=
  (complexRectangleWilsonExpectation mu rho x0 a b R T).re

/-- The fixed-coupling qualitative consequence in the normalized-potential
coupling convention, retained for the original downstream adapter. -/
def CenterNeutralQualitativePerimeterLaw
    {d n r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) : Prop :=
  3 ≤ d →
  Function.Injective sigma.ρ →
  CenterNeutral (asRepresentation rho) →
  ∀ beta : ℝ, 0 < beta →
    ∃ rate : ℝ, 0 < rate ∧
      ∀ mu : ProbabilityMeasure (Configuration d G),
        IsTranslationInvariantFreeBoundaryLimit
            sigma.wilsonPotential beta mu →
          ∀ (x0 : Site d) (a b : Fin d) (R T : ℕ),
            a ≠ b → 0 < R → 0 < T →
              complexRectangleWilsonExpectation mu rho x0 a b R T =
                  (rectangleWilsonExpectation mu rho x0 a b R T : ℂ) ∧
                Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                  rectangleWilsonExpectation mu rho x0 a b R T

/-- The coupling-uniform perimeter statement in the paper's action
normalization. The coefficient is chosen before `beta`; the normalized
Wilson potential uses coupling `n * beta`. -/
def CenterNeutralUniformCouplingPerimeterLaw
    {d n r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) : Prop :=
  3 ≤ d →
  Function.Injective sigma.ρ →
  CenterNeutral (asRepresentation rho) →
  ∃ C : ℝ, 0 < C ∧
    ∀ beta : ℝ, 0 < beta →
      ∀ mu : ProbabilityMeasure (Configuration d G),
        IsTranslationInvariantPaperFreeBoundaryLimit sigma beta mu →
          ∀ (x0 : Site d) (a b : Fin d) (R T : ℕ),
            a ≠ b → 0 < R → 0 < T →
              complexRectangleWilsonExpectation mu rho x0 a b R T =
                  (rectangleWilsonExpectation mu rho x0 a b R T : ℂ) ∧
                Real.exp (-C * (1 + beta + |Real.log beta|) *
                    (2 * (R + T) : ℕ)) ≤
                  rectangleWilsonExpectation mu rho x0 a b R T

/-- The headline theorem of the paper: one coefficient works for every
positive paper coupling and every rectangle in any common local limit. -/
abbrev CenterNeutralInfiniteVolumePerimeterLaw :=
  @CenterNeutralUniformCouplingPerimeterLaw

end

end YangMills.Gluelump.InfiniteVolume
