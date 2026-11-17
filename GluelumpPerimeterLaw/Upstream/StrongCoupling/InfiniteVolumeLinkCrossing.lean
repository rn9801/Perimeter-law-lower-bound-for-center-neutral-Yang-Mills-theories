/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionCrossingFamily
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteLinkReflectionPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryInfiniteVolume

/-!
# Infinite-volume crossing-link reflection pairings

This file passes the gauge-fixed crossing-pairing theorem through the same
ordinary free-boundary KP exhaustion used by ordinary link reflection
positivity.  The half-observable is allowed to depend on the finite
specification; only the full local observable remains fixed in the limit.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- A fixed local observable has a finite-volume crossing norm-square
certificate along the ordinary free-boundary exhaustion. -/
def EventuallyLinkCrossingNormSquare (τ : Fin d)
    (O : LocalObservable d G) : Prop :=
  ∀ᶠ n in atTop,
    ∃ F : LinkReflection.WilsonActionDecomposition.PositiveObservable G
        ((freeBoundarySpecification G d n τ).linkCrossingEdges τ 0)
        ((freeBoundarySpecification G d n τ).linkPositiveEdges τ 0),
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkPairing τ 0
        (freeBoundarySpecification_linkSymmetric n τ) O F F

/-- Strong-coupling positivity for an observable which becomes a norm square
only after crossing-link gauge fixing. -/
theorem centeredInfiniteVolume_linkCrossingReflectionPositive_half
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (O : LocalObservable d G)
    (hpair : EventuallyLinkCrossingNormSquare τ O) :
    Complex.im (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) = 0 ∧
      0 ≤ Complex.re (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) := by
  have hO := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ O
  have hre : Tendsto (fun n => Complex.re (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.re (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.im (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have hfinite : ∀ᶠ n in atTop,
      Complex.im (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, hF⟩ := hn
    let Λ := freeBoundarySpecification G d n τ
    have hfinite := Λ.linkCrossingReflectionPositive_gibbsMeasure τ 0
      (freeBoundarySpecification_linkSymmetric n τ)
      (freeBoundarySpecification_plaquetteClosed n τ) ρ hβ0 O F hF
    change Complex.im (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) O)
    rw [localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := hfinite.mono fun _ hn => hn.1
  have him' : Tendsto (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds 0) := himZero.congr' heventIm.symm
  constructor
  · exact tendsto_nhds_unique him him'
  · exact isClosed_Ici.mem_of_tendsto hre <| hfinite.mono fun _ hn => hn.2

/-- Eventual finite-volume certificates for a mixed crossing pairing and its
two diagonal norm squares. -/
def EventuallyLinkCrossingCauchySchwarz (τ : Fin d)
    (OFH OFF OHH : LocalObservable d G) : Prop :=
  ∀ᶠ n in atTop,
    ∃ (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
        ((freeBoundarySpecification G d n τ).linkCrossingEdges τ 0)
        ((freeBoundarySpecification G d n τ).linkPositiveEdges τ 0)),
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OFH F H ∧
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OFF F F ∧
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OHH H H

/-- Strong-coupling Cauchy--Schwarz for full observables which acquire their
Gram factorization only after crossing-link gauge fixing. -/
theorem centeredInfiniteVolume_linkCrossingCauchySchwarz_half
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (OFH OFF OHH : LocalObservable d G)
    (hpair : EventuallyLinkCrossingCauchySchwarz τ OFH OFF OHH) :
    Complex.normSq (∫ A, OFH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) ≤
      Complex.re (∫ A, OFF A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) *
      Complex.re (∫ A, OHH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) := by
  have hFH := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFH
  have hFF := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFF
  have hHH := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OHH
  have hlhs : Tendsto (fun n => Complex.normSq (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFH)) atTop
      (nhds (Complex.normSq (∫ A, OFH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    (Complex.continuous_normSq.continuousAt.tendsto.comp hFH)
  have hrhs : Tendsto (fun n =>
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OHH)) atTop
      (nhds (Complex.re (∫ A, OFF A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) *
        Complex.re (∫ A, OHH A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH)
  have hfinite : ∀ᶠ n in atTop,
      Complex.normSq (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFH) ≤
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OHH) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, H, hFH', hFF', hHH'⟩ := hn
    let Λ := freeBoundarySpecification G d n τ
    have hfinite := Λ.normSq_integral_gibbsMeasure_crossingPairing_le τ 0
      (freeBoundarySpecification_linkSymmetric n τ)
      (freeBoundarySpecification_plaquetteClosed n τ) ρ hβ0
      OFH OFF OHH F H hFH' hFF' hHH'
    change Complex.normSq (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OFH) ≤
      Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OFF) *
      Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OHH)
    rw [localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  exact le_of_tendsto_of_tendsto hlhs hrhs hfinite

/-- A fixed local observable has a finite Gram-family crossing norm-square
certificate along the ordinary free-boundary exhaustion. -/
def EventuallyLinkCrossingFamilyNormSquare {ι : Type*} [Fintype ι]
    (τ : Fin d) (O : LocalObservable d G) : Prop :=
  ∀ᶠ n in atTop,
    ∃ F : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
        ((freeBoundarySpecification G d n τ).linkCrossingEdges τ 0)
        ((freeBoundarySpecification G d n τ).linkPositiveEdges τ 0),
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkFamilyPairing τ 0
        (freeBoundarySpecification_linkSymmetric n τ) O F F

/-- Strong-coupling positivity for a fixed observable which becomes a finite
Gram norm square only after crossing-link gauge fixing. -/
theorem centeredInfiniteVolume_linkCrossingFamilyReflectionPositive_half
    {ι : Type*} [Fintype ι]
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (O : LocalObservable d G)
    (hpair : EventuallyLinkCrossingFamilyNormSquare (ι := ι) τ O) :
    Complex.im (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) = 0 ∧
      0 ≤ Complex.re (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) := by
  have hO := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ O
  have hre : Tendsto (fun n => Complex.re (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.re (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.im (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have hfinite : ∀ᶠ n in atTop,
      Complex.im (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, hF⟩ := hn
    let Λ := freeBoundarySpecification G d n τ
    have hfinite := Λ.linkCrossingFamilyReflectionPositive_gibbsMeasure τ 0
      (freeBoundarySpecification_linkSymmetric n τ)
      (freeBoundarySpecification_plaquetteClosed n τ) ρ hβ0 O F hF
    change Complex.im (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) O)
    rw [localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := hfinite.mono fun _ hn => hn.1
  have him' : Tendsto (fun n => Complex.im (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds 0) := himZero.congr' heventIm.symm
  constructor
  · exact tendsto_nhds_unique him him'
  · exact isClosed_Ici.mem_of_tendsto hre <| hfinite.mono fun _ hn => hn.2

/-- Eventual finite-volume certificates for a mixed finite Gram family and
its two diagonal norm squares. -/
def EventuallyLinkCrossingFamilyCauchySchwarz {ι : Type*} [Fintype ι]
    (τ : Fin d) (OFH OFF OHH : LocalObservable d G) : Prop :=
  ∀ᶠ n in atTop,
    ∃ (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
        ((freeBoundarySpecification G d n τ).linkCrossingEdges τ 0)
        ((freeBoundarySpecification G d n τ).linkPositiveEdges τ 0)),
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkFamilyPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OFH F H ∧
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkFamilyPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OFF F F ∧
      (freeBoundarySpecification G d n τ).IsGaugeFixedLinkFamilyPairing τ 0
          (freeBoundarySpecification_linkSymmetric n τ) OHH H H

/-- Strong-coupling Cauchy--Schwarz for finite Gram families which appear
only after crossing-link gauge fixing. -/
theorem centeredInfiniteVolume_linkCrossingFamilyCauchySchwarz_half
    {ι : Type*} [Fintype ι]
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (OFH OFF OHH : LocalObservable d G)
    (hpair : EventuallyLinkCrossingFamilyCauchySchwarz (ι := ι)
      τ OFH OFF OHH) :
    Complex.normSq (∫ A, OFH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) ≤
      Complex.re (∫ A, OFF A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) *
      Complex.re (∫ A, OHH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) := by
  have hFH := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFH
  have hFF := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFF
  have hHH := tendsto_freeBoundary_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OHH
  have hlhs : Tendsto (fun n => Complex.normSq (localExpectation
      (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFH)) atTop
      (nhds (Complex.normSq (∫ A, OFH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hFH
  have hrhs : Tendsto (fun n =>
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OHH)) atTop
      (nhds (Complex.re (∫ A, OFF A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) *
        Complex.re (∫ A, OHH A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH)
  have hfinite : ∀ᶠ n in atTop,
      Complex.normSq (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFH) ≤
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (freeBoundaryGibbsSequence ρ.wilsonPotential β τ n) OHH) := by
    filter_upwards [hpair] with n hn
    obtain ⟨F, H, hFH', hFF', hHH'⟩ := hn
    let Λ := freeBoundarySpecification G d n τ
    have hfinite := Λ.normSq_integral_gibbsMeasure_crossingFamilyPairing_le
      τ 0 (freeBoundarySpecification_linkSymmetric n τ)
      (freeBoundarySpecification_plaquetteClosed n τ) ρ hβ0
      OFH OFF OHH F H hFH' hFF' hHH'
    change Complex.normSq (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OFH) ≤
      Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OFF) *
      Complex.re (localExpectation
        (fullGibbsProbability Λ ρ.wilsonPotential β) OHH)
    rw [localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
    exact hfinite
  exact le_of_tendsto_of_tendsto hlhs hrhs hfinite

end

end YangMills.StrongCoupling
