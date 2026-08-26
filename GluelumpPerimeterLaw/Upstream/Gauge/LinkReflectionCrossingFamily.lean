/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionCrossing

/-!
# Finite Gram families for crossing-link reflection

A vector-valued endpoint produces a finite sum of scalar reflection pairings,
not a single scalar rank-one product.  This file equips the existing
gauge-fixed form with its finite direct-sum pairing and proves positivity and
Cauchy--Schwarz on that direct sum.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace YangMills.Gauge

noncomputable section

namespace LinkReflection.WilsonActionDecomposition

variable {G C P Q ι : Type*} {n : ℕ} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q] [Fintype ι]

/-- The direct-sum gauge-fixed pairing of two finite observable families. -/
def familyGaugeFixedPairing (D : WilsonActionDecomposition G n C P Q)
    (β : ℝ) (F H : ι → PositiveObservable G C P) : ℂ :=
  ∑ i, D.gaugeFixedPairing β (F i) (H i)

/-- A finite family paired with itself has real nonnegative gauge-fixed
pairing at nonnegative coupling. -/
theorem familyGaugeFixedPairing_self_nonneg
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F : ι → PositiveObservable G C P) :
    Complex.im (D.familyGaugeFixedPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.familyGaugeFixedPairing β F F) := by
  constructor
  · unfold familyGaugeFixedPairing
    change Complex.imAddGroupHom
      (∑ i, D.gaugeFixedPairing β (F i) (F i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [D.gaugeFixedPairing_eq_taylorPairing]
      exact (D.taylorPairing_self_nonneg hβ (F i)).1
  · unfold familyGaugeFixedPairing
    change 0 ≤ Complex.reAddGroupHom
      (∑ i, D.gaugeFixedPairing β (F i) (F i))
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ => by
      rw [D.gaugeFixedPairing_eq_taylorPairing]
      exact (D.taylorPairing_self_nonneg hβ (F i)).2

/-- Cauchy--Schwarz for the finite direct sum of gauge-fixed reflection
forms. -/
theorem normSq_familyGaugeFixedPairing_le
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F H : ι → PositiveObservable G C P) :
    Complex.normSq (D.familyGaugeFixedPairing β F H) ≤
      Complex.re (D.familyGaugeFixedPairing β F F) *
        Complex.re (D.familyGaugeFixedPairing β H H) := by
  letI : PreInnerProductSpace.Core ℂ
      (ι → PositiveObservable G C P) := {
    inner := D.familyGaugeFixedPairing β
    conj_inner_symm := fun F H => by
      unfold familyGaugeFixedPairing
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ =>
        D.gaugeFixedPairing_conj_symm β (F i) (H i)
    re_inner_nonneg := fun F =>
      (D.familyGaugeFixedPairing_self_nonneg hβ F).2
    add_left := fun F K H => by
      unfold familyGaugeFixedPairing
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        D.gaugeFixedPairing_add_left β (F i) (K i) (H i)
    smul_left := fun F H c => by
      unfold familyGaugeFixedPairing
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        D.gaugeFixedPairing_smul_left β c (F i) (H i)
  }
  have hCS := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ
    (ι → PositiveObservable G C P) _ _ _ _ F H
  change ‖D.familyGaugeFixedPairing β F H‖ *
      ‖D.familyGaugeFixedPairing β H F‖ ≤
    Complex.re (D.familyGaugeFixedPairing β F F) *
      Complex.re (D.familyGaugeFixedPairing β H H) at hCS
  have hconj : conj (D.familyGaugeFixedPairing β H F) =
      D.familyGaugeFixedPairing β F H := by
    unfold familyGaugeFixedPairing
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      D.gaugeFixedPairing_conj_symm β (F i) (H i)
  have hnorm : ‖D.familyGaugeFixedPairing β H F‖ =
      ‖D.familyGaugeFixedPairing β F H‖ := by
    rw [← hconj, Complex.norm_conj]
  rw [hnorm, ← sq, Complex.sq_norm] at hCS
  exact hCS

end LinkReflection.WilsonActionDecomposition

namespace FiniteSpecification

open Lattice.Cubic

variable {d : ℕ} {G ι : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Fintype ι]

/-- A crossing observable whose fixed-link slice is a finite Gram sum. -/
def IsGaugeFixedLinkFamilyPairing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (O : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) : Prop :=
  ∀ U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k),
    O (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) =
      ∑ i, star (F i (1, U.2.1)) *
        H i (1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)

/-- For a gauge-invariant full observable, a finite Gram factorization only
has to be checked on the slice where every crossing link is the identity. -/
theorem isGaugeFixedLinkFamilyPairing_of_gaugeInvariant
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (O : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hGauge : IsGaugeInvariant O) (hO : O.support ⊆ Λ.dynamicEdges)
    (hfixed : ∀ Uminus Uplus,
      O (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))) =
        ∑ i, star (F i (1, Uminus)) * H i (1, Uplus)) :
    Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ O F H := by
  intro U
  rw [Λ.gaugeInvariant_linkAssemble_eq_fixed τ k hΛ O hGauge hO U]
  exact hfixed U.2.1
    ((Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- At fixed crossing field, a certified finite Gram family reduces to the
direct-sum gauge-fixed pairing. -/
theorem integral_linkSides_eq_gaugeFixedFamily_of_pairing
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ O F H)
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
      (Λ.linkWilsonDecomposition τ k hΛ ρ).familyGaugeFixedPairing β F H := by
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
      ∑ i, star (F i (1, W.1)) * H i (1, W.2)
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
  simp_rw [hpoint]
  change (∫ V, K (E V) ∂sideMeasure.prod sideMeasure) = _
  rw [hE.integral_comp' K]
  change (∫ V, K V ∂sideMeasure.prod sideMeasure) =
    D.familyGaugeFixedPairing β F H
  unfold LinkReflection.WilsonActionDecomposition.familyGaugeFixedPairing
    LinkReflection.WilsonActionDecomposition.gaugeFixedPairing
  rw [← MeasureTheory.integral_finsetSum Finset.univ]
  · apply integral_congr_ae
    filter_upwards with W
    dsimp only [K]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (mul_assoc
        (Real.exp (β * D.gaugeFixedAction W) : ℂ)
        (star (F i (1, W.1))) (H i (1, W.2))).symm
  · intro i _hi
    exact D.integrable_gaugeFixedPairingIntegrand β (F i) (H i)

/-- The unnormalized finite-volume expectation of a certified finite Gram
family is its direct-sum gauge-fixed pairing. -/
theorem integral_haar_of_isGaugeFixedLinkFamilyPairing_eq
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ O F H) :
    (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
        O (Λ.evaluate V) ∂Λ.haarMeasure) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).familyGaugeFixedPairing β F H := by
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
  simp_rw [Λ.integral_linkSides_eq_gaugeFixedFamily_of_pairing
    τ k hΛ hclosed ρ β O F H hpair]
  simp

/-- Normalized Gibbs expectations of certified finite Gram families are the
positive partition-function scale of their direct-sum pairing. -/
theorem integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (O : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ O F H) :
    (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹ *
        (Λ.linkWilsonDecomposition τ k hΛ ρ).familyGaugeFixedPairing β F H := by
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
        (Λ.linkWilsonDecomposition τ k hΛ ρ).familyGaugeFixedPairing β F H := by
      rw [integral_const_mul,
        Λ.integral_haar_of_isGaugeFixedLinkFamilyPairing_eq τ k hΛ hclosed
          ρ β O F H hpair]

/-- Positivity for a full observable whose fixed crossing slice is a finite
Gram norm square. -/
theorem linkCrossingFamilyReflectionPositive_gibbsMeasure
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (O : LocalObservable d G)
    (F : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ O F F) :
    Complex.im (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) = 0 ∧
      0 ≤ Complex.re (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
    τ k hΛ hclosed ρ β O F F hpair]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  have hpos := D.familyGaugeFixedPairing_self_nonneg hβ F
  have hZ := FiniteVolume.partitionFunction_pos Λ ρ.wilsonPotential β
  have hscale :
      ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  change Complex.im
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.familyGaugeFixedPairing β F F) = 0 ∧
    0 ≤ Complex.re
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.familyGaugeFixedPairing β F F)
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hpos.1, mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) hpos.2

/-- Cauchy--Schwarz for three crossing observables represented by one finite
Gram family and its two diagonal norm squares. -/
theorem normSq_integral_gibbsMeasure_crossingFamilyPairing_le
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (OFH OFF OHH : LocalObservable d G)
    (F H : ι → LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (hFH : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ OFH F H)
    (hFF : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ OFF F F)
    (hHH : Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ OHH H H) :
    Complex.normSq (∫ V, OFH (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) ≤
      Complex.re (∫ V, OFF (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) *
      Complex.re (∫ V, OHH (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
      τ k hΛ hclosed ρ β OFH F H hFH,
    Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
      τ k hΛ hclosed ρ β OFF F F hFF,
    Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
      τ k hΛ hclosed ρ β OHH H H hHH]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  have hCS := D.normSq_familyGaugeFixedPairing_le hβ F H
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
          Complex.normSq (D.familyGaugeFixedPairing β F H) ≤
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
        (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          (Complex.re (D.familyGaugeFixedPairing β F F) *
            Complex.re (D.familyGaugeFixedPairing β H H)) := by
      gcongr
    _ = ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.familyGaugeFixedPairing β F F)) *
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.familyGaugeFixedPairing β H H)) := by ring

end FiniteSpecification

end

end YangMills.Gauge
