/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.FreeBoundaryLimitLowerBound
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightCrossing
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightExpectation
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryReflectionPositiveState

/-!
# Physical straight-line propagation in a free-boundary limit

This is the thin strong-coupling adapter for the measure-parametric
propagation theorem.  The completed-free-boundary hypothesis supplies both
the neutral reflection-positive state and the two gauge-fixed crossing-family
callbacks.  The final theorem then combines the uniform center-neutral
one-link lower bound with reflection propagation.
-/

namespace YangMills

open MeasureTheory Gauge Lattice.Cubic Wilson StrongCoupling
open Gluelump.Endpoint Gluelump.OneLink Gluelump.Propagation
open Gluelump.RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

namespace StrongCoupling

/-- Every nonnegative-coupling completed-free-boundary limit supplies the
gauge-fixed crossing-family consequences for the odd physical lengths. -/
theorem IsTranslationInvariantFreeBoundaryLimit.conjSpanLinkReflectionData
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      sigma.wilsonPotential beta mu) :
    ConjSpanLinkReflectionData mu hd sigma rho T z hz := by
  constructor
  · intro l
    exact hmu.linkCrossingFamilyPositive sigma hbeta
      (Geometry.armAxis hd)
      (conjSpanLinkStraightObservable hd sigma rho T z hz l)
      (conjSpanLinkStraight_eventuallyFamilyNormSquare
        hd sigma rho T z hz l)
  · intro l s
    exact hmu.linkCrossingFamilyCauchySchwarz sigma hbeta
      (Geometry.armAxis hd)
      (conjSpanLinkStraightMixedObservable hd sigma rho T z hz l s)
      (conjSpanLinkStraightObservable hd sigma rho T z hz l)
      (conjSpanLinkStraightObservable hd sigma rho T z hz s)
      (conjSpanLinkStraight_eventuallyFamilyCauchySchwarz
        hd sigma rho T z hz l s)

/-- A positive rate below the direct one-link expectation propagates in any
completed-free-boundary limit. -/
theorem IsTranslationInvariantFreeBoundaryLimit.conjSpanPhysicalStraightExpectation_rate_power_le
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      sigma.wilsonPotential beta mu)
    {q : ℝ} (hq : 0 < q)
    (hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1)
    {length : ℕ} (hlength : 0 < length) :
    q ^ length ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz length := by
  exact YangMills.Gluelump.Propagation.conjSpanPhysicalStraightExpectation_rate_power_le
    mu (hmu.reflectionPositiveState sigma hbeta hd)
    hd sigma rho T z hz
    (hmu.conjSpanLinkReflectionData hd sigma rho T z hz hbeta)
    hq hqseed hlength

end StrongCoupling

namespace Gluelump.Propagation

/-- End-to-end straight-line lower bound.

Center neutrality and faithfulness choose one tensor degree, one nonzero
screening intertwiner, and one positive rate before the limiting probability
measure is quantified.  The same rate then bounds every positive physical
length in every completed-free-boundary limit at the fixed positive
coupling. -/
theorem centerNeutral_exists_uniform_conjSpanPhysicalStraight_rate
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G r)
    (hcenter : CenterNeutral (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
        (tensorPower (conjSpanRep sigma) m) (asRepresentation rho),
      T ≠ 0 ∧ ∃ q : ℝ, 0 < q ∧
        ∀ mu : ProbabilityMeasure (Configuration d G),
          IsTranslationInvariantFreeBoundaryLimit
              sigma.wilsonPotential beta mu →
            ∀ {length : ℕ}, 0 < length →
              q ^ length ≤ conjSpanPhysicalStraightExpectation
                mu hd sigma rho T z hz length := by
  obtain ⟨m, T, hT, q, hq, hseed⟩ :=
    centerNeutral_exists_uniform_conjSpanOneLink_freeBoundaryLimit_lowerBound
      hd sigma hsigma rho hcenter z hz hbeta
  refine ⟨m, T, hT, q, hq, fun mu hmu length hlength ↦ ?_⟩
  have hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1 := by
    rw [conjSpanPhysicalStraightExpectation_one_eq]
    simpa only [localExpectation] using (hseed mu hmu).1
  exact hmu.conjSpanPhysicalStraightExpectation_rate_power_le
    hd sigma rho T z hz hbeta.le hq hqseed hlength

end Gluelump.Propagation

end

end YangMills
