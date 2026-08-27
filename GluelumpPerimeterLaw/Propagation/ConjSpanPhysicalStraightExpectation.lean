/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraight

/-!
# Reflection propagation for the physical-length conjugation-span line

This file is the measure-parametric propagation layer.  It assumes a neutral
`ReflectionPositiveState` and only the two gauge-fixed crossing-link
consequences that are not part of the ordinary link-positive algebra.  No
Gibbs action, thermodynamic-limit construction, or strong-coupling theorem is
imported here.

Site reflection treats the even physical lengths and crossing-link reflection
treats the odd physical lengths.  The two adjacent pointwise identities from
`ConjSpanPhysicalStraight` interlace them into one nonnegative log-convex
sequence indexed by every physical length.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The real expectation of the direct screened line of a given physical
length. -/
def conjSpanPhysicalStraightExpectation
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) : ℝ :=
  Complex.re (∫ A, conjSpanPhysicalStraightObservable
    hd sigma rho T z hz length A
      ∂(mu : Measure (Configuration d G)))

/-- At physical length one the expectation is exactly the direct one-link
seed expectation, with no rescaling or length-dependent endpoint choice. -/
theorem conjSpanPhysicalStraightExpectation_one_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) :
    conjSpanPhysicalStraightExpectation mu hd sigma rho T z hz 1 =
      Complex.re (∫ A, conjSpanReflectedOneLinkObservable
        hd sigma rho T z hz A ∂(mu : Measure (Configuration d G))) := by
  unfold conjSpanPhysicalStraightExpectation
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun A ↦
    conjSpanPhysicalStraightObservable_one_apply hd sigma rho T z hz A

/-- The two finite crossing-family consequences needed for the odd members.

The ordinary neutral `ReflectionPositiveState` intentionally does not contain
these statements: gauge fixing makes the half-observable depend on the finite
box.  A thermodynamic-limit construction can supply this small callback
interface without entering the propagation proof. -/
structure ConjSpanLinkReflectionData
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) : Prop where
  positive : ∀ l : ℕ,
    Complex.im (∫ A, conjSpanLinkStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G))) = 0 ∧
    0 ≤ Complex.re (∫ A, conjSpanLinkStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G)))
  cauchySchwarz : ∀ l s : ℕ,
    Complex.normSq (∫ A, conjSpanLinkStraightMixedObservable
      hd sigma rho T z hz l s A ∂(mu : Measure (Configuration d G))) ≤
    Complex.re (∫ A, conjSpanLinkStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G))) *
    Complex.re (∫ A, conjSpanLinkStraightObservable
      hd sigma rho T z hz s A ∂(mu : Measure (Configuration d G)))

/-- Site reflection makes every even member real and nonnegative. -/
theorem conjSpanSiteStraightIntegral_positive
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    Complex.im (∫ A, conjSpanSiteStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G))) = 0 ∧
    0 ≤ Complex.re (∫ A, conjSpanSiteStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G))) := by
  exact YangMills.Gluelump.Propagation.ReflectionPositiveState.siteReflectedObservable_positive
    hstate rho
    (conjSpanSiteStraightEndpoint hd sigma rho T z l)
    (Geometry.armAxis hd) 0 z hz
    (conjSpanSiteStraightHalfPath hd z l)
    (conjSpanSiteStraightEndpoint_supportedInSitePositiveHalf
      hd sigma rho T z hz l)
    (conjSpanSiteStraightHalfPath_supportedInSitePositiveHalf hd z hz l)

/-- The site mixed expectation at adjacent radii is the intervening odd
link-reflected self-line. -/
theorem integral_conjSpanSiteStraightMixed_succ_eq_linkStraight
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    (∫ A, conjSpanSiteStraightMixedObservable
      hd sigma rho T z hz l (l + 1) A
        ∂(mu : Measure (Configuration d G))) =
      ∫ A, conjSpanLinkStraightObservable hd sigma rho T z hz l A
        ∂(mu : Measure (Configuration d G)) := by
  apply integral_congr_ae
  exact ae_of_all _ fun A ↦
    conjSpanSiteStraightMixed_succ_apply_eq_linkStraight
      hd sigma rho T z hz l A

/-- Translation invariance identifies the adjacent link mixed expectation
with the intervening even site-reflected self-line. -/
theorem integral_conjSpanLinkStraightMixed_succ_eq_siteStraight
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    (∫ A, conjSpanLinkStraightMixedObservable
      hd sigma rho T z hz l (l + 1) A
        ∂(mu : Measure (Configuration d G))) =
      ∫ A, conjSpanSiteStraightObservable hd sigma rho T z hz (l + 1) A
        ∂(mu : Measure (Configuration d G)) := by
  calc
    _ = ∫ A, (conjSpanSiteStraightObservable
          hd sigma rho T z hz (l + 1)).translatePullback
            (unitVector (Geometry.armAxis hd)) A
        ∂(mu : Measure (Configuration d G)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun A ↦ by
        simpa only [LocalObservable.translatePullback_apply] using
          (conjSpanSiteStraight_succ_translate_apply_eq_linkMixed
            hd sigma rho T z hz l A).symm
    _ = _ := hstate.localExpectation_translatePullback
      (unitVector (Geometry.armAxis hd))
      (conjSpanSiteStraightObservable hd sigma rho T z hz (l + 1))

/-- Site Cauchy--Schwarz across adjacent even radii. -/
theorem conjSpanSiteStraightMixed_succ_cauchySchwarz
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    Complex.normSq (∫ A, conjSpanSiteStraightMixedObservable
      hd sigma rho T z hz l (l + 1) A
        ∂(mu : Measure (Configuration d G))) ≤
    Complex.re (∫ A, conjSpanSiteStraightObservable
      hd sigma rho T z hz l A ∂(mu : Measure (Configuration d G))) *
    Complex.re (∫ A, conjSpanSiteStraightObservable
      hd sigma rho T z hz (l + 1) A
        ∂(mu : Measure (Configuration d G))) := by
  exact YangMills.Gluelump.Propagation.ReflectionPositiveState.siteReflectedMixed_cauchySchwarz
    hstate rho
    (conjSpanSiteStraightEndpoint hd sigma rho T z l)
    (conjSpanSiteStraightEndpoint hd sigma rho T z (l + 1))
    (Geometry.armAxis hd) 0 z hz
    (conjSpanSiteStraightHalfPath hd z l)
    (conjSpanSiteStraightHalfPath hd z (l + 1))
    (conjSpanSiteStraightEndpoint_supportedInSitePositiveHalf
      hd sigma rho T z hz l)
    (conjSpanSiteStraightEndpoint_supportedInSitePositiveHalf
      hd sigma rho T z hz (l + 1))
    (conjSpanSiteStraightHalfPath_supportedInSitePositiveHalf hd z hz l)
    (conjSpanSiteStraightHalfPath_supportedInSitePositiveHalf
      hd z hz (l + 1))

/-- Every physical-length expectation is real. -/
theorem conjSpanPhysicalStraightExpectation_im_eq_zero
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz)
    (length : ℕ) :
    Complex.im (∫ A, conjSpanPhysicalStraightObservable
      hd sigma rho T z hz length A
        ∂(mu : Measure (Configuration d G))) = 0 := by
  rcases Nat.even_or_odd' length with ⟨l, rfl | rfl⟩
  · simpa using
      (conjSpanSiteStraightIntegral_positive
        mu hstate hd sigma rho T z hz l).1
  · simpa using hlink.positive l |>.1

/-- Reflection positivity makes the physical-length sequence nonnegative. -/
theorem conjSpanPhysicalStraightExpectation_nonneg
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz) :
    ∀ length : ℕ,
      0 ≤ conjSpanPhysicalStraightExpectation
        mu hd sigma rho T z hz length := by
  intro length
  rcases Nat.even_or_odd' length with ⟨l, rfl | rfl⟩
  · simpa [conjSpanPhysicalStraightExpectation] using
      (conjSpanSiteStraightIntegral_positive
        mu hstate hd sigma rho T z hz l).2
  · simpa [conjSpanPhysicalStraightExpectation] using hlink.positive l |>.2

/-- Alternating site and crossing-link Cauchy--Schwarz gives adjacent
log-convexity at every physical length. -/
theorem conjSpanPhysicalStraightExpectation_reflectionLogConvex
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz) :
    ReflectionLogConvex
      (conjSpanPhysicalStraightExpectation mu hd sigma rho T z hz) := by
  intro length
  rcases Nat.even_or_odd' length with ⟨l, rfl | rfl⟩
  · have hcs := conjSpanSiteStraightMixed_succ_cauchySchwarz
      mu hstate hd sigma rho T z hz l
    rw [integral_conjSpanSiteStraightMixed_succ_eq_linkStraight
      mu hd sigma rho T z hz l] at hcs
    have him := (hlink.positive l).1
    rw [Complex.normSq_apply, him, mul_zero, add_zero] at hcs
    have hright : 2 * l + 2 = 2 * (l + 1) := by omega
    rw [hright]
    simpa only [conjSpanPhysicalStraightExpectation,
      conjSpanPhysicalStraightObservable_even,
      conjSpanPhysicalStraightObservable_odd, pow_two] using hcs
  · have hcs := hlink.cauchySchwarz l (l + 1)
    rw [integral_conjSpanLinkStraightMixed_succ_eq_siteStraight
      mu hstate hd sigma rho T z hz l] at hcs
    have him := (conjSpanSiteStraightIntegral_positive
      mu hstate hd sigma rho T z hz (l + 1)).1
    rw [Complex.normSq_apply, him, mul_zero, add_zero] at hcs
    have hmiddle : 2 * l + 1 + 1 = 2 * (l + 1) := by omega
    have hright : 2 * l + 1 + 2 = 2 * (l + 1) + 1 := by omega
    rw [hmiddle, hright]
    simpa only [conjSpanPhysicalStraightExpectation,
      conjSpanPhysicalStraightObservable_even,
      conjSpanPhysicalStraightObservable_odd, pow_two] using hcs

/-- Every physical-length expectation is at most one. -/
theorem conjSpanPhysicalStraightExpectation_le_one
    (mu : ProbabilityMeasure (Configuration d G))
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) :
    conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz length ≤ 1 := by
  calc
    _ ≤ ‖∫ A, conjSpanPhysicalStraightObservable
        hd sigma rho T z hz length A
          ∂(mu : Measure (Configuration d G))‖ := Complex.re_le_norm _
    _ ≤ 1 := by
      have hbound : ∀ᵐ A ∂(mu : Measure (Configuration d G)),
          ‖conjSpanPhysicalStraightObservable
            hd sigma rho T z hz length A‖ ≤ 1 :=
        ae_of_all _ fun A ↦
          norm_conjSpanPhysicalStraightObservable_le_one
            hd sigma rho T z hz length A
      simpa using norm_integral_le_of_norm_le_const
        (μ := (mu : Measure (Configuration d G))) (C := (1 : ℝ))
        (f := fun A ↦ conjSpanPhysicalStraightObservable
          hd sigma rho T z hz length A) hbound

/-- Strict positivity of the one-link member propagates to every physical
length. -/
theorem conjSpanPhysicalStraightExpectation_pos
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz)
    (hone : 0 < conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1) :
    ∀ length : ℕ,
      0 < conjSpanPhysicalStraightExpectation
        mu hd sigma rho T z hz length :=
  positive_of_reflectionLogConvex_of_pos
    (conjSpanPhysicalStraightExpectation_reflectionLogConvex
      mu hstate hd sigma rho T z hz hlink)
    (conjSpanPhysicalStraightExpectation_nonneg
      mu hstate hd sigma rho T z hz hlink)
    (by omega : 0 < (1 : ℕ)) hone

/-- The direct one-link expectation is a lower-bound base for every positive
physical length. -/
theorem conjSpanPhysicalStraightExpectation_first_power_le
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz)
    (hone : 0 < conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1)
    {length : ℕ} (hlength : 0 < length) :
    conjSpanPhysicalStraightExpectation mu hd sigma rho T z hz 1 ^ length ≤
      conjSpanPhysicalStraightExpectation
        mu hd sigma rho T z hz length := by
  exact first_power_le_of_pos
    (conjSpanPhysicalStraightExpectation_reflectionLogConvex
      mu hstate hd sigma rho T z hz hlink)
    (conjSpanPhysicalStraightExpectation_pos
      mu hstate hd sigma rho T z hz hlink hone)
    (conjSpanPhysicalStraightExpectation_le_one
      mu hd sigma rho T z hz 0)
    hlength

/-- Any specified positive rate below the one-link expectation propagates
to every positive physical length. -/
theorem conjSpanPhysicalStraightExpectation_rate_power_le
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hlink : ConjSpanLinkReflectionData mu hd sigma rho T z hz)
    {q : ℝ} (hq : 0 < q)
    (hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1)
    {length : ℕ} (hlength : 0 < length) :
    q ^ length ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz length := by
  have hone : 0 < conjSpanPhysicalStraightExpectation
      mu hd sigma rho T z hz 1 := hq.trans_le hqseed
  exact (pow_le_pow_left₀ hq.le hqseed length).trans
    (conjSpanPhysicalStraightExpectation_first_power_le
      mu hstate hd sigma rho T z hz hlink hone hlength)

end

end YangMills.Gluelump.Propagation
