/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.CenterScreening
import YangMills.Lattice.Plaquette
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryInfiniteVolume
import GluelumpPerimeterLaw.Upstream.Wilson.Loop

/-!
# Target statement: center-neutral perimeter law in a thermodynamic limit

This file records the human-facing gluelump perimeter-law target for a
translation-invariant infinite-volume limit of completed free-boundary boxes.
It contains definitions, culminating in the proposition
`CenterNeutralInfiniteVolumePerimeterLaw`; it does not postulate that
proposition as an axiom.

The thermodynamic-limit hypothesis is explicit: every local observable must
converge from each coordinate-oriented family of completed reflection boxes,
and the limiting probability must be translation invariant.  The first part
lets all reflection inequalities pass to one common state; the second lets
the propagation argument move its local reflected geometries.

The order of quantifiers records the allowed dependencies.  At fixed positive
coupling, the positive perimeter rate depends only on the dimension and the
action and Wilson representations.  It is independent of the chosen limiting
probability, rectangle location, coordinate plane, and side lengths.
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

/-- **Main target proposition: infinite-volume center-neutral perimeter law.**

For a faithful action representation `sigma` and a center-neutral Wilson
representation `rho` in dimension at least three, every
translation-invariant completed-free-boundary thermodynamic limit satisfies a
uniform perimeter lower bound at positive coupling.

The proof is `centerNeutralInfiniteVolumePerimeterLaw` in
`YangMills.Gluelump.InfiniteVolumePerimeterLaw`; this definition keeps the
human-facing quantifier order and conclusion separately inspectable. -/
def CenterNeutralInfiniteVolumePerimeterLaw
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

end

end YangMills.Gluelump.InfiniteVolume
