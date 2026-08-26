/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.AntiDiagonalReflection
import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflectionPositivity
import GluelumpPerimeterLaw.Upstream.Gauge.InfiniteReflection
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Reflection-positive probability states

This file is the measure-level interface used by reflection propagation.  It
contains no thermodynamic-limit construction and no strong-coupling input.
The individual predicates say exactly that the corresponding reflected
pairing is positive/Hermitian on its positive local algebra; the bundled
certificate additionally records translation and coordinate-reflection
invariance.

All fields are properties of one probability measure.  Consequently a
gluelump propagation theorem can depend on this interface without depending
on polymers, cluster expansions, or a particular construction of the state.
-/

open Filter MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- Reflection positivity through the integer plane `x τ = k`. -/
def MeasureSiteReflectionPositive
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F : LocalObservable d G, F.SupportedInSitePositiveHalf τ k →
    Complex.im (∫ A, F.siteReflectionProduct τ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.siteReflectionProduct τ k F A ∂μ)

/-- Site-reflection pairing of two local observables. -/
def measureSiteReflectionPairing
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.siteReflectionProduct τ k H A ∂μ

/-- Cauchy--Schwarz for the site-reflection pairing. -/
def MeasureSiteReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F H : LocalObservable d G,
    F.SupportedInSitePositiveHalf τ k →
    H.SupportedInSitePositiveHalf τ k →
    Complex.normSq (measureSiteReflectionPairing μ τ k F H) ≤
      Complex.re (measureSiteReflectionPairing μ τ k F F) *
        Complex.re (measureSiteReflectionPairing μ τ k H H)

/-- Reflection positivity through the half-integer plane `x τ = k+1/2`.
The ordinary positive algebra consists of gauge-invariant observables. -/
def MeasureLinkReflectionPositive
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F : LocalObservable d G, F.SupportedInLinkPositiveHalf τ k →
    IsGaugeInvariant F →
    Complex.im (∫ A, F.linkReflectionProduct τ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.linkReflectionProduct τ k F A ∂μ)

/-- Link-reflection pairing of two local observables. -/
def measureLinkReflectionPairing
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.linkReflectionProduct τ k H A ∂μ

/-- Cauchy--Schwarz for the gauge-invariant link-reflection algebra. -/
def MeasureLinkReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F H : LocalObservable d G,
    F.SupportedInLinkPositiveHalf τ k →
    H.SupportedInLinkPositiveHalf τ k →
    IsGaugeInvariant F → IsGaugeInvariant H →
    Complex.normSq (measureLinkReflectionPairing μ τ k F H) ≤
      Complex.re (measureLinkReflectionPairing μ τ k F F) *
        Complex.re (measureLinkReflectionPairing μ τ k H H)

/-- Reflection positivity through `x τ - x σ = k`. -/
def MeasureDiagonalReflectionPositive
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    Complex.im (∫ A, F.diagonalReflectionProduct τ σ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.diagonalReflectionProduct τ σ k F A ∂μ)

/-- Diagonal-reflection pairing of two local observables. -/
def measureDiagonalReflectionPairing
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.diagonalReflectionProduct τ σ k H A ∂μ

/-- Cauchy--Schwarz for the diagonal-reflection pairing. -/
def MeasureDiagonalReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    H.SupportedInDiagonalPositiveHalf τ σ k →
    Complex.normSq (measureDiagonalReflectionPairing μ τ σ k F H) ≤
      Complex.re (measureDiagonalReflectionPairing μ τ σ k F F) *
        Complex.re (measureDiagonalReflectionPairing μ τ σ k H H)

/-- Hermitian symmetry of the diagonal-reflection pairing. -/
def MeasureDiagonalReflectionHermitian
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    H.SupportedInDiagonalPositiveHalf τ σ k →
    star (measureDiagonalReflectionPairing μ τ σ k H F) =
      measureDiagonalReflectionPairing μ τ σ k F H

/-- Reflection positivity through `x τ + x σ = k`. -/
def MeasureAntiDiagonalReflectionPositive
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    Complex.im (∫ A, F.antiDiagonalReflectionProduct τ σ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.antiDiagonalReflectionProduct τ σ k F A ∂μ)

/-- Anti-diagonal-reflection pairing of two local observables. -/
def measureAntiDiagonalReflectionPairing
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.antiDiagonalReflectionProduct τ σ k H A ∂μ

/-- Cauchy--Schwarz for the anti-diagonal-reflection pairing. -/
def MeasureAntiDiagonalReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    H.SupportedInAntiDiagonalPositiveHalf τ σ k →
    Complex.normSq (measureAntiDiagonalReflectionPairing μ τ σ k F H) ≤
      Complex.re (measureAntiDiagonalReflectionPairing μ τ σ k F F) *
        Complex.re (measureAntiDiagonalReflectionPairing μ τ σ k H H)

/-- Hermitian symmetry of the anti-diagonal-reflection pairing. -/
def MeasureAntiDiagonalReflectionHermitian
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInAntiDiagonalPositiveHalf τ σ k →
    H.SupportedInAntiDiagonalPositiveHalf τ σ k →
    star (measureAntiDiagonalReflectionPairing μ τ σ k H F) =
      measureAntiDiagonalReflectionPairing μ τ σ k F H

/-- Invariance of a measure under every lattice translation. -/
def IsTranslationInvariant
    (μ : Measure (Configuration d G)) : Prop :=
  ∀ v : Site d,
    Measure.map (LocalObservable.translateConfiguration (G := G) v) μ = μ

/-- Invariance under reflection of any coordinate through the origin. -/
def IsCoordinateReflectionInvariant
    (μ : Measure (Configuration d G)) : Prop :=
  ∀ τ : Fin d, Measure.map (siteReflectConfiguration (G := G) τ 0) μ = μ

/-- Coordinate-reflection invariance as an integral identity. -/
theorem IsCoordinateReflectionInvariant.integral_siteReflectionPullback
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsCoordinateReflectionInvariant (mu : Measure (Configuration d G)))
    (tau : Fin d) (F : LocalObservable d G) :
    (∫ A, F.siteReflectionPullback tau 0 A
      ∂(mu : Measure (Configuration d G))) =
      ∫ A, F A ∂(mu : Measure (Configuration d G)) := by
  have hreflect :=
    (continuous_siteReflectConfiguration (G := G) tau 0).measurable
  simp only [LocalObservable.siteReflectionPullback_apply]
  change (∫ A, F (siteReflectConfiguration tau 0 A)
      ∂(mu : Measure (Configuration d G))) =
    ∫ A, F A ∂(mu : Measure (Configuration d G))
  calc
    _ = ∫ A, F A ∂Measure.map (siteReflectConfiguration (G := G) tau 0)
        (mu : Measure (Configuration d G)) := by
      rw [MeasureTheory.integral_map hreflect.aemeasurable
        F.toContinuousMap.continuous.aestronglyMeasurable]
    _ = _ := by rw [h tau]

/-- Coordinate-flip invariance identifies the anti-diagonal pairing with a
diagonal pairing of pulled-back observables. -/
theorem measureAntiDiagonalReflectionPairing_eq_diagonal
    {mu : ProbabilityMeasure (Configuration d G)}
    (hinv : IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)))
    (tau sigma : Fin d) (k : ℤ) (F H : LocalObservable d G) :
    measureAntiDiagonalReflectionPairing (mu : Measure _) tau sigma k F H =
      measureDiagonalReflectionPairing (mu : Measure _) tau sigma k
        (F.siteReflectionPullback sigma 0)
        (H.siteReflectionPullback sigma 0) := by
  let O := F.antiDiagonalReflectionProduct tau sigma k H
  have hinvO := hinv.integral_siteReflectionPullback sigma O
  unfold measureAntiDiagonalReflectionPairing measureDiagonalReflectionPairing
  calc
    (∫ A, O A ∂(mu : Measure _)) =
        ∫ A, O (siteReflectConfiguration sigma 0 A) ∂(mu : Measure _) :=
      by simpa only [LocalObservable.siteReflectionPullback_apply] using hinvO.symm
    _ = ∫ A,
        (F.siteReflectionPullback sigma 0).diagonalReflectionProduct
          tau sigma k (H.siteReflectionPullback sigma 0) A
          ∂(mu : Measure _) := by
      apply integral_congr_ae
      exact ae_of_all _ fun A => by
        simpa only [LocalObservable.siteReflectionPullback_apply] using
          F.antiDiagonalReflectionProduct_siteReflectionPullback_apply
            tau sigma k H A

/-- Anti-diagonal RP follows from diagonal RP by a coordinate flip. -/
theorem MeasureAntiDiagonalReflectionPositive.of_diagonal
    {mu : ProbabilityMeasure (Configuration d G)}
    (hinv : IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    (hdiag : MeasureDiagonalReflectionPositive
      (mu : Measure (Configuration d G)) tau sigma k) :
    MeasureAntiDiagonalReflectionPositive
      (mu : Measure (Configuration d G)) tau sigma k := by
  intro _ F hF
  have hpos := hdiag hts (F.siteReflectionPullback sigma 0)
    (hF.siteReflectionPullback hts)
  change Complex.im (measureAntiDiagonalReflectionPairing
      (mu : Measure _) tau sigma k F F) = 0 ∧
    0 ≤ Complex.re (measureAntiDiagonalReflectionPairing
      (mu : Measure _) tau sigma k F F)
  rw [measureAntiDiagonalReflectionPairing_eq_diagonal hinv]
  exact hpos

/-- Anti-diagonal Cauchy--Schwarz follows from its diagonal counterpart. -/
theorem MeasureAntiDiagonalReflectionCauchySchwarz.of_diagonal
    {mu : ProbabilityMeasure (Configuration d G)}
    (hinv : IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    (hdiag : MeasureDiagonalReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) tau sigma k) :
    MeasureAntiDiagonalReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) tau sigma k := by
  intro _ F H hF hH
  have hcs := hdiag hts
    (F.siteReflectionPullback sigma 0) (H.siteReflectionPullback sigma 0)
    (hF.siteReflectionPullback hts) (hH.siteReflectionPullback hts)
  rw [measureAntiDiagonalReflectionPairing_eq_diagonal hinv,
    measureAntiDiagonalReflectionPairing_eq_diagonal hinv,
    measureAntiDiagonalReflectionPairing_eq_diagonal hinv]
  exact hcs

/-- Anti-diagonal Hermitian symmetry follows from its diagonal counterpart. -/
theorem MeasureAntiDiagonalReflectionHermitian.of_diagonal
    {mu : ProbabilityMeasure (Configuration d G)}
    (hinv : IsCoordinateReflectionInvariant
      (mu : Measure (Configuration d G)))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    (hdiag : MeasureDiagonalReflectionHermitian
      (mu : Measure (Configuration d G)) tau sigma k) :
    MeasureAntiDiagonalReflectionHermitian
      (mu : Measure (Configuration d G)) tau sigma k := by
  intro _ F H hF hH
  have hherm := hdiag hts
    (F.siteReflectionPullback sigma 0) (H.siteReflectionPullback sigma 0)
    (hF.siteReflectionPullback hts) (hH.siteReflectionPullback hts)
  rw [measureAntiDiagonalReflectionPairing_eq_diagonal hinv,
    measureAntiDiagonalReflectionPairing_eq_diagonal hinv]
  exact hherm

/-- Translation invariance as an integral identity for local observables. -/
theorem IsTranslationInvariant.integral_translatePullback
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : IsTranslationInvariant (mu : Measure (Configuration d G)))
    (v : Site d) (F : LocalObservable d G) :
    (∫ A, F.translatePullback v A ∂(mu : Measure (Configuration d G))) =
      ∫ A, F A ∂(mu : Measure (Configuration d G)) := by
  have hv :=
    (LocalObservable.continuous_translateConfiguration (G := G) v).measurable
  change (∫ A, F (LocalObservable.translateConfiguration v A)
      ∂(mu : Measure (Configuration d G))) =
    ∫ A, F A ∂(mu : Measure (Configuration d G))
  calc
    _ = ∫ A, F A ∂Measure.map
        (LocalObservable.translateConfiguration (G := G) v)
        (mu : Measure (Configuration d G)) := by
      rw [MeasureTheory.integral_map hv.aemeasurable
        F.toContinuousMap.continuous.aestronglyMeasurable]
    _ = _ := by rw [h v]

/-- Translation invariance moves site RP from the origin to every integer
parallel plane. -/
theorem MeasureSiteReflectionPositive.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    (τ : Fin d)
    (hzero : MeasureSiteReflectionPositive
      (mu : Measure (Configuration d G)) τ 0) :
    ∀ k : ℤ, MeasureSiteReflectionPositive
      (mu : Measure (Configuration d G)) τ k := by
  intro k F hF
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInSitePositiveHalf τ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    change 0 ≤ Lattice.Cubic.translate v a.source τ
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hpos := hzero Ft hFt
  have htranslate := htrans.integral_translatePullback v
    (F.siteReflectionProduct τ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.siteReflectionProduct τ k F).translatePullback v A =
        Ft.siteReflectionProduct τ 0 Ft A := by
    intro A
    change star (F (siteReflectConfiguration τ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (siteReflectConfiguration τ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_siteReflect_axis_neg]
  have heq :
      (∫ A, F.siteReflectionProduct τ k F A ∂(mu : Measure _)) =
        ∫ A, Ft.siteReflectionProduct τ 0 Ft A ∂(mu : Measure _) := by
    rw [← htranslate]
    exact integral_congr_ae (ae_of_all _ hintegrand)
  rw [heq]
  exact hpos

/-- Translation invariance moves site Cauchy--Schwarz from the origin to all
integer parallel planes. -/
theorem MeasureSiteReflectionCauchySchwarz.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    (τ : Fin d)
    (hzero : MeasureSiteReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ 0) :
    ∀ k : ℤ, MeasureSiteReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ k := by
  intro k F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInSitePositiveHalf τ k) :
      (K.translatePullback v).SupportedInSitePositiveHalf τ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    change 0 ≤ Lattice.Cubic.translate v a.source τ
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hCS := hzero Ft Ht (translateSupport F hF) (translateSupport H hH)
  have pairing_translate (K L : LocalObservable d G) :
      measureSiteReflectionPairing (mu : Measure _) τ k K L =
        measureSiteReflectionPairing (mu : Measure _) τ 0
          (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := htrans.integral_translatePullback v
      (K.siteReflectionProduct τ k L)
    rw [measureSiteReflectionPairing, measureSiteReflectionPairing,
      ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (siteReflectConfiguration τ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (siteReflectConfiguration τ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_siteReflect_axis_neg]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

/-- Translation invariance moves link RP from the plane at `1/2` to every
parallel half-integer plane. -/
theorem MeasureLinkReflectionPositive.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    (τ : Fin d)
    (hhalf : MeasureLinkReflectionPositive
      (mu : Measure (Configuration d G)) τ 0) :
    ∀ k : ℤ, MeasureLinkReflectionPositive
      (mu : Measure (Configuration d G)) τ k := by
  intro k F hF hGauge
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInLinkPositiveHalf τ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    rw [PositiveEdge.target_translate]
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hGaugeFt : IsGaugeInvariant Ft :=
    LocalObservable.IsGaugeInvariant.translatePullback hGauge v
  have hpos := hhalf Ft hFt hGaugeFt
  have htranslate := htrans.integral_translatePullback v
    (F.linkReflectionProduct τ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.linkReflectionProduct τ k F).translatePullback v A =
        Ft.linkReflectionProduct τ 0 Ft A := by
    intro A
    change star (F (linkReflectConfiguration τ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (linkReflectConfiguration τ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_linkReflect_axis_neg]
  have heq :
      (∫ A, F.linkReflectionProduct τ k F A ∂(mu : Measure _)) =
        ∫ A, Ft.linkReflectionProduct τ 0 Ft A ∂(mu : Measure _) := by
    rw [← htranslate]
    exact integral_congr_ae (ae_of_all _ hintegrand)
  rw [heq]
  exact hpos

/-- Translation invariance moves link Cauchy--Schwarz from `1/2` to every
parallel half-integer plane. -/
theorem MeasureLinkReflectionCauchySchwarz.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    (τ : Fin d)
    (hhalf : MeasureLinkReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ 0) :
    ∀ k : ℤ, MeasureLinkReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ k := by
  intro k F H hF hH hGaugeF hGaugeH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInLinkPositiveHalf τ k) :
      (K.translatePullback v).SupportedInLinkPositiveHalf τ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    rw [PositiveEdge.target_translate]
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hCS := hhalf Ft Ht (translateSupport F hF) (translateSupport H hH)
    (LocalObservable.IsGaugeInvariant.translatePullback hGaugeF v)
    (LocalObservable.IsGaugeInvariant.translatePullback hGaugeH v)
  have pairing_translate (K L : LocalObservable d G) :
      measureLinkReflectionPairing (mu : Measure _) τ k K L =
        measureLinkReflectionPairing (mu : Measure _) τ 0
          (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := htrans.integral_translatePullback v
      (K.linkReflectionProduct τ k L)
    rw [measureLinkReflectionPairing, measureLinkReflectionPairing,
      ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (linkReflectConfiguration τ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (linkReflectConfiguration τ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_linkReflect_axis_neg]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

/-- Translation invariance moves diagonal RP from the origin to all affine
parallel diagonal planes. -/
theorem MeasureDiagonalReflectionPositive.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : MeasureDiagonalReflectionPositive
      (mu : Measure (Configuration d G)) τ σ 0) :
    ∀ k : ℤ, MeasureDiagonalReflectionPositive
      (mu : Measure (Configuration d G)) τ σ k := by
  intro k _ F hF
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hpos := hzero hτσ Ft hFt
  have htranslate := htrans.integral_translatePullback v
    (F.diagonalReflectionProduct τ σ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.diagonalReflectionProduct τ σ k F).translatePullback v A =
        Ft.diagonalReflectionProduct τ σ 0 Ft A := by
    intro A
    change star (F (diagonalReflectConfiguration τ σ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (diagonalReflectConfiguration τ σ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  have heq :
      (∫ A, F.diagonalReflectionProduct τ σ k F A ∂(mu : Measure _)) =
        ∫ A, Ft.diagonalReflectionProduct τ σ 0 Ft A
          ∂(mu : Measure _) := by
    rw [← htranslate]
    exact integral_congr_ae (ae_of_all _ hintegrand)
  rw [heq]
  exact hpos

/-- Translation invariance moves diagonal Cauchy--Schwarz from the origin to
all affine parallel planes. -/
theorem MeasureDiagonalReflectionCauchySchwarz.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : MeasureDiagonalReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ σ 0) :
    ∀ k : ℤ, MeasureDiagonalReflectionCauchySchwarz
      (mu : Measure (Configuration d G)) τ σ k := by
  intro k _ F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInDiagonalPositiveHalf τ σ k) :
      (K.translatePullback v).SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hCS := hzero hτσ Ft Ht (translateSupport F hF)
    (translateSupport H hH)
  have pairing_translate (K L : LocalObservable d G) :
      measureDiagonalReflectionPairing (mu : Measure _) τ σ k K L =
        measureDiagonalReflectionPairing (mu : Measure _) τ σ 0
          (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := htrans.integral_translatePullback v
      (K.diagonalReflectionProduct τ σ k L)
    rw [measureDiagonalReflectionPairing, measureDiagonalReflectionPairing,
      ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (diagonalReflectConfiguration τ σ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (diagonalReflectConfiguration τ σ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

/-- Translation invariance moves diagonal Hermitian symmetry from the origin
to all affine parallel planes. -/
theorem MeasureDiagonalReflectionHermitian.all_planes
    {mu : ProbabilityMeasure (Configuration d G)}
    (htrans : IsTranslationInvariant (mu : Measure (Configuration d G)))
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : MeasureDiagonalReflectionHermitian
      (mu : Measure (Configuration d G)) τ σ 0) :
    ∀ k : ℤ, MeasureDiagonalReflectionHermitian
      (mu : Measure (Configuration d G)) τ σ k := by
  intro k _ F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInDiagonalPositiveHalf τ σ k) :
      (K.translatePullback v).SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hHerm := hzero hτσ Ft Ht (translateSupport F hF)
    (translateSupport H hH)
  have pairing_translate (K L : LocalObservable d G) :
      measureDiagonalReflectionPairing (mu : Measure _) τ σ k K L =
        measureDiagonalReflectionPairing (mu : Measure _) τ σ 0
          (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := htrans.integral_translatePullback v
      (K.diagonalReflectionProduct τ σ k L)
    rw [measureDiagonalReflectionPairing, measureDiagonalReflectionPairing,
      ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (diagonalReflectConfiguration τ σ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (diagonalReflectConfiguration τ σ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  rw [pairing_translate H F, pairing_translate F H]
  exact hHerm

/-- Neutral reflection-positive-state interface used by gluelump propagation.

The predicates are required at every affine cut.  Finite-family versions are
derived from the scalar positivity/Cauchy--Schwarz fields by summing the
families; gauge-fixed crossing-link families use the separate completed-box
limit interface because their half-observables depend on the box. -/
structure ReflectionPositiveState
    (μ : ProbabilityMeasure (Configuration d G)) : Prop where
  translationInvariant : IsTranslationInvariant (μ : Measure (Configuration d G))
  coordinateReflectionInvariant :
    IsCoordinateReflectionInvariant (μ : Measure (Configuration d G))
  sitePositive : ∀ τ k,
    MeasureSiteReflectionPositive (μ : Measure (Configuration d G)) τ k
  siteCauchySchwarz : ∀ τ k,
    MeasureSiteReflectionCauchySchwarz (μ : Measure (Configuration d G)) τ k
  linkPositive : ∀ τ k,
    MeasureLinkReflectionPositive (μ : Measure (Configuration d G)) τ k
  linkCauchySchwarz : ∀ τ k,
    MeasureLinkReflectionCauchySchwarz (μ : Measure (Configuration d G)) τ k
  diagonalPositive : ∀ τ σ k,
    MeasureDiagonalReflectionPositive (μ : Measure (Configuration d G)) τ σ k
  diagonalCauchySchwarz : ∀ τ σ k,
    MeasureDiagonalReflectionCauchySchwarz (μ : Measure (Configuration d G)) τ σ k
  diagonalHermitian : ∀ τ σ k,
    MeasureDiagonalReflectionHermitian (μ : Measure (Configuration d G)) τ σ k
  antiDiagonalPositive : ∀ τ σ k,
    MeasureAntiDiagonalReflectionPositive (μ : Measure (Configuration d G)) τ σ k
  antiDiagonalCauchySchwarz : ∀ τ σ k,
    MeasureAntiDiagonalReflectionCauchySchwarz
      (μ : Measure (Configuration d G)) τ σ k
  antiDiagonalHermitian : ∀ τ σ k,
    MeasureAntiDiagonalReflectionHermitian (μ : Measure (Configuration d G)) τ σ k

/-- Direct sum of scalar site-reflection pairings. -/
def measureSiteReflectionFamilyPairing {iota : Type*} [Fintype iota]
    (mu : Measure (Configuration d G)) (tau : Fin d) (k : ℤ)
    (F H : iota → LocalObservable d G) : ℂ :=
  ∑ i, measureSiteReflectionPairing mu tau k (F i) (H i)

/-- Positivity of every scalar component implies positivity and reality of a
finite site-reflection norm square. -/
theorem ReflectionPositiveState.siteFamilyPositive
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] (tau : Fin d) (k : ℤ)
    (F : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInSitePositiveHalf tau k) :
    Complex.im (measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau k F F) = 0 ∧
    0 ≤ Complex.re (measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau k F F) := by
  constructor
  · unfold measureSiteReflectionFamilyPairing
    change Complex.imAddGroupHom
      (∑ i, measureSiteReflectionPairing (mu : Measure _) tau k (F i) (F i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => (hstate.sitePositive tau k (F i) (hF i)).1
  · unfold measureSiteReflectionFamilyPairing
    change 0 ≤ Complex.reAddGroupHom
      (∑ i, measureSiteReflectionPairing (mu : Measure _) tau k (F i) (F i))
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ => (hstate.sitePositive tau k (F i) (hF i)).2

/-- Scalar site RP and Cauchy--Schwarz imply Cauchy--Schwarz on every finite
direct sum. -/
theorem ReflectionPositiveState.siteFamilyCauchySchwarz
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] (tau : Fin d) (k : ℤ)
    (F H : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInSitePositiveHalf tau k)
    (hH : ∀ i, (H i).SupportedInSitePositiveHalf tau k) :
    Complex.normSq (measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau k F H) ≤
      (∑ i, Complex.re (measureSiteReflectionPairing
        (mu : Measure (Configuration d G)) tau k (F i) (F i))) *
      ∑ i, Complex.re (measureSiteReflectionPairing
        (mu : Measure (Configuration d G)) tau k (H i) (H i)) := by
  let p : iota → ℂ := fun i =>
    measureSiteReflectionPairing (mu : Measure _) tau k (F i) (H i)
  let a : iota → ℝ := fun i => Complex.re
    (measureSiteReflectionPairing (mu : Measure _) tau k (F i) (F i))
  let b : iota → ℝ := fun i => Complex.re
    (measureSiteReflectionPairing (mu : Measure _) tau k (H i) (H i))
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := by
    intro i _
    exact (hstate.sitePositive tau k (F i) (hF i)).2
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := by
    intro i _
    exact (hstate.sitePositive tau k (H i) (hH i)).2
  have hp : ∀ i ∈ Finset.univ, ‖p i‖ ^ 2 ≤ a i * b i := by
    intro i _
    rw [Complex.sq_norm]
    exact hstate.siteCauchySchwarz tau k (F i) (H i) (hF i) (hH i)
  have hsumNorm : ‖∑ i, p i‖ ≤ ∑ i, ‖p i‖ := norm_sum_le Finset.univ p
  calc
    Complex.normSq (measureSiteReflectionFamilyPairing
        (mu : Measure _) tau k F H) = ‖∑ i, p i‖ ^ 2 := by
      rw [Complex.sq_norm]
      rfl
    _ ≤ (∑ i, ‖p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsumNorm 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ha hb hp
    _ = _ := rfl

/-- Direct sum of scalar diagonal-reflection pairings. -/
def measureDiagonalReflectionFamilyPairing {iota : Type*} [Fintype iota]
    (mu : Measure (Configuration d G)) (tau sigma : Fin d) (k : ℤ)
    (F H : iota → LocalObservable d G) : ℂ :=
  ∑ i, measureDiagonalReflectionPairing mu tau sigma k (F i) (H i)

/-- Reality and positivity of a finite diagonal norm-square family. -/
theorem ReflectionPositiveState.diagonalFamilyPositive
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] {tau sigma : Fin d}
    (hts : tau ≠ sigma) (k : ℤ)
    (F : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInDiagonalPositiveHalf tau sigma k) :
    Complex.im (measureDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F F) = 0 ∧
    0 ≤ Complex.re (measureDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F F) := by
  constructor
  · unfold measureDiagonalReflectionFamilyPairing
    change Complex.imAddGroupHom
      (∑ i, measureDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ =>
      (hstate.diagonalPositive tau sigma k hts (F i) (hF i)).1
  · unfold measureDiagonalReflectionFamilyPairing
    change 0 ≤ Complex.reAddGroupHom
      (∑ i, measureDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i))
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ =>
      (hstate.diagonalPositive tau sigma k hts (F i) (hF i)).2

/-- Cauchy--Schwarz for every finite direct sum of diagonal pairings. -/
theorem ReflectionPositiveState.diagonalFamilyCauchySchwarz
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] {tau sigma : Fin d}
    (hts : tau ≠ sigma) (k : ℤ)
    (F H : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInDiagonalPositiveHalf tau sigma k)
    (hH : ∀ i, (H i).SupportedInDiagonalPositiveHalf tau sigma k) :
    Complex.normSq (measureDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F H) ≤
      (∑ i, Complex.re (measureDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i))) *
      ∑ i, Complex.re (measureDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (H i) (H i)) := by
  let p : iota → ℂ := fun i =>
    measureDiagonalReflectionPairing (mu : Measure _) tau sigma k (F i) (H i)
  let a : iota → ℝ := fun i => Complex.re
    (measureDiagonalReflectionPairing (mu : Measure _) tau sigma k (F i) (F i))
  let b : iota → ℝ := fun i => Complex.re
    (measureDiagonalReflectionPairing (mu : Measure _) tau sigma k (H i) (H i))
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := by
    intro i _
    exact (hstate.diagonalPositive tau sigma k hts (F i) (hF i)).2
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := by
    intro i _
    exact (hstate.diagonalPositive tau sigma k hts (H i) (hH i)).2
  have hp : ∀ i ∈ Finset.univ, ‖p i‖ ^ 2 ≤ a i * b i := by
    intro i _
    rw [Complex.sq_norm]
    exact hstate.diagonalCauchySchwarz tau sigma k hts
      (F i) (H i) (hF i) (hH i)
  have hsumNorm : ‖∑ i, p i‖ ≤ ∑ i, ‖p i‖ := norm_sum_le Finset.univ p
  calc
    Complex.normSq (measureDiagonalReflectionFamilyPairing
        (mu : Measure _) tau sigma k F H) = ‖∑ i, p i‖ ^ 2 := by
      rw [Complex.sq_norm]
      rfl
    _ ≤ (∑ i, ‖p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsumNorm 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ha hb hp
    _ = _ := rfl

/-- Direct sum of scalar anti-diagonal-reflection pairings. -/
def measureAntiDiagonalReflectionFamilyPairing {iota : Type*} [Fintype iota]
    (mu : Measure (Configuration d G)) (tau sigma : Fin d) (k : ℤ)
    (F H : iota → LocalObservable d G) : ℂ :=
  ∑ i, measureAntiDiagonalReflectionPairing mu tau sigma k (F i) (H i)

/-- Reality and positivity of a finite anti-diagonal norm-square family. -/
theorem ReflectionPositiveState.antiDiagonalFamilyPositive
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] {tau sigma : Fin d}
    (hts : tau ≠ sigma) (k : ℤ)
    (F : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInAntiDiagonalPositiveHalf tau sigma k) :
    Complex.im (measureAntiDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F F) = 0 ∧
    0 ≤ Complex.re (measureAntiDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F F) := by
  constructor
  · unfold measureAntiDiagonalReflectionFamilyPairing
    change Complex.imAddGroupHom
      (∑ i, measureAntiDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i)) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ =>
      (hstate.antiDiagonalPositive tau sigma k hts (F i) (hF i)).1
  · unfold measureAntiDiagonalReflectionFamilyPairing
    change 0 ≤ Complex.reAddGroupHom
      (∑ i, measureAntiDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i))
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ =>
      (hstate.antiDiagonalPositive tau sigma k hts (F i) (hF i)).2

/-- Cauchy--Schwarz for every finite direct sum of anti-diagonal pairings. -/
theorem ReflectionPositiveState.antiDiagonalFamilyCauchySchwarz
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    {iota : Type*} [Fintype iota] {tau sigma : Fin d}
    (hts : tau ≠ sigma) (k : ℤ)
    (F H : iota → LocalObservable d G)
    (hF : ∀ i, (F i).SupportedInAntiDiagonalPositiveHalf tau sigma k)
    (hH : ∀ i, (H i).SupportedInAntiDiagonalPositiveHalf tau sigma k) :
    Complex.normSq (measureAntiDiagonalReflectionFamilyPairing
      (mu : Measure _) tau sigma k F H) ≤
      (∑ i, Complex.re (measureAntiDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (F i) (F i))) *
      ∑ i, Complex.re (measureAntiDiagonalReflectionPairing
        (mu : Measure _) tau sigma k (H i) (H i)) := by
  let p : iota → ℂ := fun i =>
    measureAntiDiagonalReflectionPairing
      (mu : Measure _) tau sigma k (F i) (H i)
  let a : iota → ℝ := fun i => Complex.re
    (measureAntiDiagonalReflectionPairing
      (mu : Measure _) tau sigma k (F i) (F i))
  let b : iota → ℝ := fun i => Complex.re
    (measureAntiDiagonalReflectionPairing
      (mu : Measure _) tau sigma k (H i) (H i))
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := by
    intro i _
    exact (hstate.antiDiagonalPositive tau sigma k hts (F i) (hF i)).2
  have hb : ∀ i ∈ Finset.univ, 0 ≤ b i := by
    intro i _
    exact (hstate.antiDiagonalPositive tau sigma k hts (H i) (hH i)).2
  have hp : ∀ i ∈ Finset.univ, ‖p i‖ ^ 2 ≤ a i * b i := by
    intro i _
    rw [Complex.sq_norm]
    exact hstate.antiDiagonalCauchySchwarz tau sigma k hts
      (F i) (H i) (hF i) (hH i)
  have hsumNorm : ‖∑ i, p i‖ ≤ ∑ i, ‖p i‖ := norm_sum_le Finset.univ p
  calc
    Complex.normSq (measureAntiDiagonalReflectionFamilyPairing
        (mu : Measure _) tau sigma k F H) = ‖∑ i, p i‖ ^ 2 := by
      rw [Complex.sq_norm]
      rfl
    _ ≤ (∑ i, ‖p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsumNorm 2
    _ ≤ (∑ i, a i) * ∑ i, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ ha hb hp
    _ = _ := rfl

/-- Translation invariance gives the expectation identity used throughout
measure-parametric propagation. -/
theorem ReflectionPositiveState.localExpectation_translatePullback
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : ReflectionPositiveState mu) (v : Site d)
    (F : LocalObservable d G) :
    (∫ A, F.translatePullback v A ∂(mu : Measure (Configuration d G))) =
      ∫ A, F A ∂(mu : Measure (Configuration d G)) := by
  have hv :=
    (LocalObservable.continuous_translateConfiguration (G := G) v).measurable
  change (∫ A, F (LocalObservable.translateConfiguration v A)
      ∂(mu : Measure (Configuration d G))) =
    ∫ A, F A ∂(mu : Measure (Configuration d G))
  calc
    _ = ∫ A, F A ∂Measure.map
        (LocalObservable.translateConfiguration (G := G) v)
        (mu : Measure (Configuration d G)) := by
      rw [MeasureTheory.integral_map hv.aemeasurable
        F.toContinuousMap.continuous.aestronglyMeasurable]
    _ = _ := by rw [h.translationInvariant v]

/-- Coordinate-reflection invariance gives the corresponding expectation
identity. -/
theorem ReflectionPositiveState.localExpectation_siteReflectionPullback
    {mu : ProbabilityMeasure (Configuration d G)}
    (h : ReflectionPositiveState mu) (τ : Fin d)
    (F : LocalObservable d G) :
    (∫ A, F.siteReflectionPullback τ 0 A
      ∂(mu : Measure (Configuration d G))) =
      ∫ A, F A ∂(mu : Measure (Configuration d G)) := by
  have hreflect := (continuous_siteReflectConfiguration (G := G) τ 0).measurable
  simp only [LocalObservable.siteReflectionPullback_apply]
  change (∫ A, F (siteReflectConfiguration τ 0 A)
      ∂(mu : Measure (Configuration d G))) =
    ∫ A, F A ∂(mu : Measure (Configuration d G))
  calc
    _ = ∫ A, F A ∂Measure.map (siteReflectConfiguration (G := G) τ 0)
        (mu : Measure (Configuration d G)) := by
      rw [MeasureTheory.integral_map hreflect.aemeasurable
        F.toContinuousMap.continuous.aestronglyMeasurable]
    _ = _ := by rw [h.coordinateReflectionInvariant τ]

end

end YangMills.Gauge
