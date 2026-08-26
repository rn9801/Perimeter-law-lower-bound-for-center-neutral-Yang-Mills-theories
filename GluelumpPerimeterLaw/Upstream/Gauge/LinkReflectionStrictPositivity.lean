/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionCrossingFamily

/-!
# Strict link-reflection positivity from a detected Taylor word

Ordinary reflection positivity only uses that every Taylor/Fubini Gram term is
nonnegative.  Strict positivity needs one more, genuinely representation-
theoretic input: at least one cross-plane matrix-coefficient word must have a
nonzero weighted overlap with the half observable.  This file isolates that
input and proves that it makes the full gauge-fixed reflection norm strict.
-/

open MeasureTheory

namespace YangMills.Gauge.LinkReflection

open Complex
open scoped BigOperators ComplexConjugate
open scoped Topology
open Filter Set

noncomputable section

variable {G : Type*} {n : ℕ} {C P Q : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [T2Space G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q]

namespace WilsonActionDecomposition

variable (D : WilsonActionDecomposition G n C P Q)

/-- A half observable is detected at coupling `beta` when one labelled
cross-plane Taylor word has nonzero weighted amplitude.  For a faithful action
representation this is the finite-dimensional Stone--Weierstrass/spin-network
input in the Seiler argument. -/
def TaylorDetected (beta : ℝ) (F : PositiveObservable G C P) : Prop :=
  ∃ (m : ℕ) (w : CrossWord Q n m), D.taylorAmplitude beta F w ≠ 0

omit [Fintype C] in
/-- Each fixed Taylor-word amplitude varies continuously with the coupling. -/
theorem continuous_taylorAmplitude
    (F : PositiveObservable G C P) {m : ℕ} (w : CrossWord Q n m) :
    Continuous fun beta : ℝ => D.taylorAmplitude beta F w := by
  unfold taylorAmplitude
  have h := continuous_parametric_integral_of_continuous
    (μ := sideHaar (G := G) (P := P))
    (s := Set.univ)
    (f := fun beta : ℝ => fun U : SideConfiguration G P =>
      (Real.exp (beta * D.positiveAction U) : ℂ) * F (1, U) *
        D.crossMonomial w U)
    (by
      have haction : Continuous fun x : ℝ × SideConfiguration G P =>
          x.1 * D.positiveAction x.2 :=
        continuous_fst.mul (D.positiveAction.continuous.comp continuous_snd)
      have hF : Continuous fun x : ℝ × SideConfiguration G P => F (1, x.2) :=
        F.continuous.comp (continuous_const.prodMk continuous_snd)
      have hword : Continuous fun x : ℝ × SideConfiguration G P =>
          D.crossMonomial w x.2 :=
        (D.continuous_crossMonomial w).comp continuous_snd
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp haction)).mul hF |>.mul hword)
    isCompact_univ
  simpa using h

omit [Fintype C] in
/-- A Taylor word detected at the independent-Haar point remains detected for
all sufficiently small couplings. -/
theorem eventually_taylorDetected_of_amplitude_zero_ne
    (F : PositiveObservable G C P) {m : ℕ} (w : CrossWord Q n m)
    (hw : D.taylorAmplitude 0 F w ≠ 0) :
    ∀ᶠ beta in 𝓝 0, D.TaylorDetected beta F := by
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hne : ∀ᶠ beta in 𝓝 0, D.taylorAmplitude beta F w ∈ ({0}ᶜ : Set ℂ) :=
    (D.continuous_taylorAmplitude F w).continuousAt
      (hopen.mem_nhds (by simpa using hw))
  exact hne.mono fun beta hbeta => ⟨m, w, by simpa using hbeta⟩

omit [Fintype C] in
theorem re_taylorGramTerm_self_pos_of_amplitude_ne_zero
    {beta : ℝ} (hbeta : 0 < beta)
    (F : PositiveObservable G C P) {m : ℕ} (w : CrossWord Q n m)
    (hw : D.taylorAmplitude beta F w ≠ 0) :
    0 < Complex.re ((D.taylorCoefficient beta m : ℂ) *
      ∑ v : CrossWord Q n m,
        star (D.taylorAmplitude beta F v) * D.taylorAmplitude beta F v) := by
  have hcoeff : 0 < D.taylorCoefficient beta m := by
    unfold taylorCoefficient
    positivity [D.representation.dimension_pos]
  have hsum : 0 < ∑ v : CrossWord Q n m,
      ‖D.taylorAmplitude beta F v‖ ^ 2 := by
    apply lt_of_lt_of_le (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))
    exact Finset.single_le_sum
      (f := fun v : CrossWord Q n m =>
        ‖D.taylorAmplitude beta F v‖ ^ 2)
      (fun _ _ => sq_nonneg _)
      (Finset.mem_univ w)
  rw [show (∑ v : CrossWord Q n m,
      star (D.taylorAmplitude beta F v) * D.taylorAmplitude beta F v) =
      ((∑ v : CrossWord Q n m,
        ‖D.taylorAmplitude beta F v‖ ^ 2 : ℝ) : ℂ) by
      push_cast
      apply Finset.sum_congr rfl
      intro v _hv
      change conj (D.taylorAmplitude beta F v) *
        D.taylorAmplitude beta F v = _
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ofReal_zero, mul_zero, sub_zero]
  exact mul_pos hcoeff hsum

omit [Fintype C] in
/-- If one cross-plane word detects the half observable, the exact
Taylor/Fubini reflection norm is strictly positive. -/
theorem taylorPairing_self_pos_of_detected
    {beta : ℝ} (hbeta : 0 < beta) (F : PositiveObservable G C P)
    (hdetect : D.TaylorDetected beta F) :
    0 < Complex.re (D.taylorPairing beta F F) := by
  obtain ⟨m, w, hw⟩ := hdetect
  let term : ℕ → ℂ := fun k => (D.taylorCoefficient beta k : ℂ) *
    ∑ v : CrossWord Q n k,
      star (D.taylorAmplitude beta F v) * D.taylorAmplitude beta F v
  have hterm : Summable term := by
    have hint := D.summable_integral_taylorIntegrand beta F F
    apply hint.congr
    intro k
    exact D.integral_taylorIntegrand_eq_gram beta F F k
  have hreSummable : Summable (fun k => Complex.re (term k)) := by
    apply Summable.of_norm
    exact hterm.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => Complex.abs_re_le_norm (term k))
  have hnonneg : ∀ k, 0 ≤ Complex.re (term k) := fun k =>
    (D.taylorGramTerm_self_nonneg hbeta.le F k).2
  have hmpos : 0 < Complex.re (term m) := by
    exact D.re_taylorGramTerm_self_pos_of_amplitude_ne_zero hbeta F w hw
  have hmle : Complex.re (term m) ≤ ∑' k, Complex.re (term k) := by
    have h := Summable.sum_le_tsum (s := {m})
      (fun k _hk => hnonneg k) hreSummable
    simpa using h
  unfold taylorPairing
  change 0 < Complex.re (∑' k, term k)
  rw [Complex.re_tsum hterm]
  exact hmpos.trans_le hmle

omit [Fintype C] in
/-- Any selected word gives an explicit nonnegative lower bound on the full
Taylor reflection norm.  This is the quantitative form needed to retain the
endpoint factor in the one-link estimate. -/
theorem taylorCoefficient_mul_normSq_amplitude_le_re_taylorPairing
    {beta : ℝ} (hbeta : 0 ≤ beta) (F : PositiveObservable G C P)
    {m : ℕ} (w : CrossWord Q n m) :
    D.taylorCoefficient beta m * ‖D.taylorAmplitude beta F w‖ ^ 2 ≤
      Complex.re (D.taylorPairing beta F F) := by
  let term : ℕ → ℂ := fun k => (D.taylorCoefficient beta k : ℂ) *
    ∑ v : CrossWord Q n k,
      star (D.taylorAmplitude beta F v) * D.taylorAmplitude beta F v
  have hterm : Summable term := by
    have hint := D.summable_integral_taylorIntegrand beta F F
    apply hint.congr
    intro k
    exact D.integral_taylorIntegrand_eq_gram beta F F k
  have hreSummable : Summable (fun k => Complex.re (term k)) := by
    apply Summable.of_norm
    exact hterm.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => Complex.abs_re_le_norm (term k))
  have hnonneg : ∀ k, 0 ≤ Complex.re (term k) := fun k =>
    (D.taylorGramTerm_self_nonneg hbeta F k).2
  have hselected : D.taylorCoefficient beta m *
      ‖D.taylorAmplitude beta F w‖ ^ 2 ≤ Complex.re (term m) := by
    have hcoeff := D.taylorCoefficient_nonneg hbeta m
    have hsingle : ‖D.taylorAmplitude beta F w‖ ^ 2 ≤
        ∑ v : CrossWord Q n m, ‖D.taylorAmplitude beta F v‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun v : CrossWord Q n m =>
          ‖D.taylorAmplitude beta F v‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ w)
    have hsum : (∑ v : CrossWord Q n m,
        star (D.taylorAmplitude beta F v) * D.taylorAmplitude beta F v) =
        ((∑ v : CrossWord Q n m,
          ‖D.taylorAmplitude beta F v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro v _hv
      change conj (D.taylorAmplitude beta F v) *
        D.taylorAmplitude beta F v = _
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    dsimp only [term]
    rw [hsum, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left hsingle hcoeff
  have hmle : Complex.re (term m) ≤ ∑' k, Complex.re (term k) := by
    have h := Summable.sum_le_tsum (s := {m})
      (fun k _hk => hnonneg k) hreSummable
    simpa using h
  unfold taylorPairing
  change _ ≤ Complex.re (∑' k, term k)
  rw [Complex.re_tsum hterm]
  exact hselected.trans hmle

omit [Fintype C] in
/-- Strict positivity of the gauge-fixed link-reflection norm. -/
theorem gaugeFixedPairing_self_pos_of_detected
    {beta : ℝ} (hbeta : 0 < beta) (F : PositiveObservable G C P)
    (hdetect : D.TaylorDetected beta F) :
    0 < Complex.re (D.gaugeFixedPairing beta F F) := by
  rw [D.gaugeFixedPairing_eq_taylorPairing]
  exact D.taylorPairing_self_pos_of_detected hbeta F hdetect

omit [Fintype C] in
/-- Quantitative selected-word lower bound for the gauge-fixed pairing. -/
theorem taylorCoefficient_mul_normSq_amplitude_le_re_gaugeFixedPairing
    {beta : ℝ} (hbeta : 0 ≤ beta) (F : PositiveObservable G C P)
    {m : ℕ} (w : CrossWord Q n m) :
    D.taylorCoefficient beta m * ‖D.taylorAmplitude beta F w‖ ^ 2 ≤
      Complex.re (D.gaugeFixedPairing beta F F) := by
  rw [D.gaugeFixedPairing_eq_taylorPairing]
  exact D.taylorCoefficient_mul_normSq_amplitude_le_re_taylorPairing
    hbeta F w

omit [Fintype C] in
/-- A single detected component makes the whole finite endpoint Gram family
strictly positive.  The remaining components contribute nonnegative diagonal
reflection norms. -/
theorem familyGaugeFixedPairing_self_pos_of_detected
    {ι : Type*} [Fintype ι] {beta : ℝ} (hbeta : 0 < beta)
    (F : ι → PositiveObservable G C P)
    (hdetect : ∃ i, D.TaylorDetected beta (F i)) :
    0 < Complex.re (D.familyGaugeFixedPairing beta F F) := by
  obtain ⟨i, hi⟩ := hdetect
  have hipos : 0 < Complex.re (D.gaugeFixedPairing beta (F i) (F i)) :=
    D.gaugeFixedPairing_self_pos_of_detected hbeta (F i) hi
  unfold familyGaugeFixedPairing
  change 0 < Complex.reAddGroupHom
    (∑ j, D.gaugeFixedPairing beta (F j) (F j))
  rw [map_sum]
  change 0 < ∑ j, Complex.re (D.gaugeFixedPairing beta (F j) (F j))
  refine hipos.trans_le (Finset.single_le_sum
    (f := fun j => Complex.re (D.gaugeFixedPairing beta (F j) (F j))) ?_ ?_)
  · intro j _hj
    dsimp only
    rw [D.gaugeFixedPairing_eq_taylorPairing]
    exact (D.taylorPairing_self_nonneg hbeta.le (F j)).2
  · exact Finset.mem_univ i

omit [Fintype C] in
/-- Quantitative lower bound contributed by one component and one Taylor word
inside the endpoint Gram family. -/
theorem taylorCoefficient_mul_normSq_amplitude_le_re_familyGaugeFixedPairing
    {ι : Type*} [Fintype ι] {beta : ℝ} (hbeta : 0 ≤ beta)
    (F : ι → PositiveObservable G C P) (i : ι)
    {m : ℕ} (w : CrossWord Q n m) :
    D.taylorCoefficient beta m * ‖D.taylorAmplitude beta (F i) w‖ ^ 2 ≤
      Complex.re (D.familyGaugeFixedPairing beta F F) := by
  have hcomponent :=
    D.taylorCoefficient_mul_normSq_amplitude_le_re_gaugeFixedPairing
      hbeta (F i) w
  unfold familyGaugeFixedPairing
  change _ ≤ Complex.reAddGroupHom
    (∑ j, D.gaugeFixedPairing beta (F j) (F j))
  rw [map_sum]
  change _ ≤ ∑ j, Complex.re (D.gaugeFixedPairing beta (F j) (F j))
  refine hcomponent.trans (Finset.single_le_sum
    (f := fun j => Complex.re (D.gaugeFixedPairing beta (F j) (F j))) ?_ ?_)
  · intro j _hj
    dsimp only
    rw [D.gaugeFixedPairing_eq_taylorPairing]
    exact (D.taylorPairing_self_nonneg hbeta (F j)).2
  · exact Finset.mem_univ i

end WilsonActionDecomposition

namespace FiniteSpecification

open Lattice.Cubic

variable {d : ℕ} {ι : Type*}

/-- A detected endpoint component upgrades finite-volume link-reflection
positivity to strict positivity, with the entire endpoint Gram-family factor
retained. -/
theorem linkCrossingFamilyReflectionStrictlyPositive_gibbsMeasure
    (Λ : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric tau k) (hclosed : Λ.PlaquetteClosed)
    (rho : Wilson.ContinuousUnitaryRepData G n) {beta : ℝ}
    (hbeta : 0 < beta) (O : LocalObservable d G)
    [Fintype ι]
    (F : ι → WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges tau k) (Λ.linkPositiveEdges tau k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing tau k hΛ O F F)
    (hdetect : ∃ i,
      (Λ.linkWilsonDecomposition tau k hΛ rho).TaylorDetected beta (F i)) :
    0 < Complex.re (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ rho.wilsonPotential beta) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
    tau k hΛ hclosed rho beta O F F hpair]
  let D := Λ.linkWilsonDecomposition tau k hΛ rho
  have hfamily : 0 < Complex.re (D.familyGaugeFixedPairing beta F F) :=
    D.familyGaugeFixedPairing_self_pos_of_detected hbeta F hdetect
  have hZ := FiniteVolume.partitionFunction_pos Λ rho.wilsonPotential beta
  have hscale :
      ((FiniteVolume.partitionFunction Λ rho.wilsonPotential beta : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ rho.wilsonPotential beta)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (inv_pos.mpr hZ) hfamily

/-- The normalized finite Gibbs expectation retains the explicit contribution
of any chosen endpoint component and Taylor word. -/
theorem linkCrossingFamilyReflection_gibbsMeasure_selectedWord_lowerBound
    (Λ : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric tau k) (hclosed : Λ.PlaquetteClosed)
    (rho : Wilson.ContinuousUnitaryRepData G n) {beta : ℝ}
    (hbeta : 0 ≤ beta) (O : LocalObservable d G)
    [Fintype ι]
    (F : ι → WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges tau k) (Λ.linkPositiveEdges tau k))
    (hpair : Λ.IsGaugeFixedLinkFamilyPairing tau k hΛ O F F)
    (i : ι) {m : ℕ}
    (w : WilsonActionDecomposition.CrossWord
      (Λ.linkCrossPlaquettes tau k) n m) :
    (FiniteVolume.partitionFunction Λ rho.wilsonPotential beta)⁻¹ *
        ((Λ.linkWilsonDecomposition tau k hΛ rho).taylorCoefficient beta m *
          ‖(Λ.linkWilsonDecomposition tau k hΛ rho).taylorAmplitude
            beta (F i) w‖ ^ 2) ≤
      Complex.re (∫ V, O (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ rho.wilsonPotential beta) := by
  rw [Λ.integral_gibbsMeasure_of_isGaugeFixedLinkFamilyPairing_eq
    tau k hΛ hclosed rho beta O F F hpair]
  let D := Λ.linkWilsonDecomposition tau k hΛ rho
  have hfamily :=
    D.taylorCoefficient_mul_normSq_amplitude_le_re_familyGaugeFixedPairing
      hbeta F i w
  have hZ := FiniteVolume.partitionFunction_pos Λ rho.wilsonPotential beta
  have hscale :
      ((FiniteVolume.partitionFunction Λ rho.wilsonPotential beta : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ rho.wilsonPotential beta)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hfamily (inv_nonneg.mpr hZ.le)

end FiniteSpecification

end

end YangMills.Gauge.LinkReflection
