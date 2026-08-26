/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionBridge

/-!
# Link reflection for observables crossing the reflection plane

The ordinary link-reflection API asks the positive-half observable itself to
be gauge invariant.  An open Wilson half-line with a covariant endpoint need
not satisfy that condition.  What is actually used by the crossing-forest
proof is weaker: after the crossing links have been gauge fixed to `1`, the
full observable factors into a conjugate left half times a right half.

This file records that exact certificate and proves positivity and
Cauchy--Schwarz directly from the existing gauge-fixed Taylor--Fubini Gram
form.  No new positivity input is introduced.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G]
  [GaugeHaarProbability G]

/-- A full local observable crossing a half-integer plane is a certified
reflection pairing when, after the one-sided crossing-link gauge fix, it is
exactly a conjugate left half times a right half. -/
def IsGaugeFixedLinkPairing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (O : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) : Prop :=
  ∀ U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k),
    O (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) =
      star (F (1, U.2.1)) *
        H (1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] in
/-- To certify a gauge-invariant full observable, it suffices to factor it on
the slice where every crossing link is `1`.  Gauge invariance supplies exactly
the configuration-dependent one-sided gauge transformation needed to reach
that slice.  In particular, neither half factor is required to be gauge
invariant by itself. -/
theorem isGaugeFixedLinkPairing_of_gaugeInvariant
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (O : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hGauge : IsGaugeInvariant O) (hO : O.support ⊆ Λ.dynamicEdges)
    (hfixed : ∀ Uminus Uplus,
      O (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))) =
        star (F (1, Uminus)) * H (1, Uplus)) :
    Λ.IsGaugeFixedLinkPairing τ k hΛ O F H := by
  intro U
  rw [Λ.gaugeInvariant_linkAssemble_eq_fixed τ k hΛ O hGauge hO U]
  exact hfixed U.2.1
    ((Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)

/-- At fixed crossing field, a certified crossing observable reduces to the
same gauge-fixed Gram pairing as an ordinary link-reflection product. -/
theorem integral_linkSides_eq_gaugeFixed_of_isGaugeFixedLinkPairing
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkPairing τ k hΛ O F H)
    (Ucross : LinkReflection.CrossingConfiguration G
      (Λ.linkCrossingEdges τ k)) :
    (∫ V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
        LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k),
      (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.linkAssemble τ k hΛ (Ucross, V))) : ℂ) *
        O (Λ.evaluate (Λ.linkAssemble τ k hΛ (Ucross, V)))
      ∂(LinkReflection.WilsonActionDecomposition.sideHaar
          (G := G) (P := Λ.linkPositiveEdges τ k)).prod
        (LinkReflection.WilsonActionDecomposition.sideHaar
          (G := G) (P := Λ.linkPositiveEdges τ k))) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β F H := by
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  let sideMeasure := LinkReflection.WilsonActionDecomposition.sideHaar
    (G := G) (P := Λ.linkPositiveEdges τ k)
  let Eplus := (Λ.linkCrossingGaugeFix τ k).fixSideEquiv Ucross
  let E : (LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) ≃ᵐ
      (LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) :=
    (MeasurableEquiv.refl _).prodCongr Eplus
  have hE : MeasurePreserving E (sideMeasure.prod sideMeasure)
      (sideMeasure.prod sideMeasure) :=
    MeasurePreserving.prod (MeasurePreserving.id _)
      ((Λ.linkCrossingGaugeFix τ k).measurePreserving_fixSideEquiv Ucross)
  let K : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) → ℂ :=
    fun W => (Real.exp (β * D.gaugeFixedAction W) : ℂ) *
      star (F (1, W.1)) * H (1, W.2)
  have hpoint : ∀ V, (Real.exp (β * FiniteVolume.action Λ
        ρ.wilsonPotential (Λ.linkAssemble τ k hΛ (Ucross, V))) : ℂ) *
      O (Λ.evaluate (Λ.linkAssemble τ k hΛ (Ucross, V))) = K (E V) := by
    intro V
    rw [Λ.action_linkAssemble_eq_fixed τ k hΛ hclosed ρ (Ucross, V),
      Λ.action_linkAssemble_fixed τ k hΛ hclosed ρ
        (V.1, (Λ.linkCrossingGaugeFix τ k).fixSide Ucross V.2),
      hpair (Ucross, V)]
    have hEV : E V =
        (V.1, (Λ.linkCrossingGaugeFix τ k).fixSide Ucross V.2) := rfl
    rw [hEV]
    simp [K, D]
    ring
  simp_rw [hpoint]
  change (∫ V, K (E V) ∂sideMeasure.prod sideMeasure) = _
  rw [hE.integral_comp' K]
  rfl

/-- The unnormalized finite-volume expectation of a certified crossing
observable is the existing gauge-fixed Taylor--Fubini pairing. -/
theorem integral_haar_of_isGaugeFixedLinkPairing_eq
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkPairing τ k hΛ O F H) :
    (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
        O (Λ.evaluate V) ∂Λ.haarMeasure) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β F H := by
  let Kdyn : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
      O (Λ.evaluate V)
  have hKdyn : Continuous Kdyn := by
    unfold Kdyn
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul
          (FiniteVolume.continuous_action Λ ρ.wilsonPotential)))).mul
      (O.toContinuousMap.continuous.comp Λ.continuous_evaluate)
  have hchange :
      (∫ U, Kdyn (Λ.linkAssemble τ k hΛ U)
          ∂LinkReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ V, Kdyn V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_linkAssemble τ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.linkAssemble τ k hΛ).continuous.measurable.aemeasurable
      hKdyn.measurable.aestronglyMeasurable).symm
  rw [← hchange]
  let Kref : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) → ℂ := fun U =>
    (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential
      (Λ.linkAssemble τ k hΛ U)) : ℂ) *
      O (Λ.evaluate (Λ.linkAssemble τ k hΛ U))
  have hKref : Integrable Kref
      LinkReflection.WilsonActionDecomposition.reflectedHaar := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    unfold Kref
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((FiniteVolume.continuous_action Λ ρ.wilsonPotential).comp
            (Λ.linkAssemble τ k hΛ).continuous)))).mul
      (O.toContinuousMap.continuous.comp
        (Λ.continuous_evaluate.comp (Λ.linkAssemble τ k hΛ).continuous))
  change (∫ U, Kref U
    ∂LinkReflection.WilsonActionDecomposition.reflectedHaar) = _
  unfold LinkReflection.WilsonActionDecomposition.reflectedHaar
  rw [integral_prod _ hKref]
  simp only [Kref]
  simp_rw [Λ.integral_linkSides_eq_gaugeFixed_of_isGaugeFixedLinkPairing
    τ k hΛ hclosed ρ β O F H hpair]
  simp

/-- Normalized Gibbs expectations of certified crossing observables are
exactly the positive partition-function scale of the gauge-fixed pairing. -/
theorem integral_gibbsMeasure_of_isGaugeFixedLinkPairing_eq
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkPairing τ k hΛ O F H) :
    (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹ *
        (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β F H := by
  rw [FiniteVolume.gibbsMeasure, integral_tilted]
  let Z := FiniteVolume.partitionFunction Λ ρ.wilsonPotential β
  change (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
      Z : ℝ) • O (Λ.evaluate V) ∂Λ.haarMeasure) = _
  calc
    _ = ∫ V, (Z : ℂ)⁻¹ *
        ((Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
          O (Λ.evaluate V)) ∂Λ.haarMeasure := by
      apply integral_congr_ae
      filter_upwards with V
      change ((Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
          Z : ℝ) : ℂ) * O (Λ.evaluate V) = _
      rw [Complex.ofReal_div, div_eq_mul_inv]
      ring
    _ = (Z : ℂ)⁻¹ *
        (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β F H := by
      rw [integral_const_mul,
        Λ.integral_haar_of_isGaugeFixedLinkPairing_eq τ k hΛ hclosed
          ρ β O F H hpair]

/-- Positivity for a full observable which becomes a norm square only after
the crossing links are gauge fixed to the identity. -/
theorem linkCrossingReflectionPositive_gibbsMeasure
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (O : LocalObservable d G)
    (F : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkPairing τ k hΛ O F F) :
    Complex.im (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) = 0 ∧
      0 ≤ Complex.re (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkPairing_eq τ k hΛ hclosed
    ρ β O F F hpair]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  have hpos : Complex.im (D.gaugeFixedPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gaugeFixedPairing β F F) := by
    rw [D.gaugeFixedPairing_eq_taylorPairing]
    exact D.taylorPairing_self_nonneg hβ F
  have hZ := FiniteVolume.partitionFunction_pos Λ ρ.wilsonPotential β
  have hscale :
      ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  change Complex.im
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.gaugeFixedPairing β F F) = 0 ∧
    0 ≤ Complex.re
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.gaugeFixedPairing β F F)
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hpos.1, mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) hpos.2

/-- Cauchy--Schwarz for three crossing observables which become respectively
`⟨F,H⟩`, `⟨F,F⟩`, and `⟨H,H⟩` after crossing-link gauge fixing. -/
theorem normSq_integral_gibbsMeasure_crossingPairing_le
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (OFH OFF OHH : LocalObservable d G)
    (F H : LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hFH : Λ.IsGaugeFixedLinkPairing τ k hΛ OFH F H)
    (hFF : Λ.IsGaugeFixedLinkPairing τ k hΛ OFF F F)
    (hHH : Λ.IsGaugeFixedLinkPairing τ k hΛ OHH H H) :
    Complex.normSq (∫ V, OFH (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) ≤
      Complex.re (∫ V, OFF (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) *
      Complex.re (∫ V, OHH (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkPairing_eq τ k hΛ hclosed
      ρ β OFH F H hFH,
    Λ.integral_gibbsMeasure_of_isGaugeFixedLinkPairing_eq τ k hΛ hclosed
      ρ β OFF F F hFF,
    Λ.integral_gibbsMeasure_of_isGaugeFixedLinkPairing_eq τ k hΛ hclosed
      ρ β OHH H H hHH]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  have hCS := D.normSq_gaugeFixedPairing_le hβ F H
  have hZ := FiniteVolume.partitionFunction_pos Λ ρ.wilsonPotential β
  have hscale :
      ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hs : 0 ≤ (FiniteVolume.partitionFunction Λ
      ρ.wilsonPotential β)⁻¹ := inv_nonneg.mpr hZ.le
  calc
    (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
        (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.normSq (D.gaugeFixedPairing β F H) ≤
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
        (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          (Complex.re (D.gaugeFixedPairing β F F) *
            Complex.re (D.gaugeFixedPairing β H H)) := by
      gcongr
    _ = ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.gaugeFixedPairing β F F)) *
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.gaugeFixedPairing β H H)) := by ring

end FiniteSpecification

end

end YangMills.Gauge
