/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.CrossFeatureSplit
import GluelumpPerimeterLaw.Upstream.Gauge.LinkReflectionCrossingFamily

/-!
# Concrete endpoint/remote factorization of the link-reflection pairing

This file connects the lattice-independent split-kernel API to the existing
gauge-fixed Wilson action.  The side-coordinate split is measure preserving,
and the normalized Wilson potential fixes the Taylor parameter to
`beta / (2 * n)`.  No volume-dependent constant is discarded.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Gauge.LinkReflection
open scoped BigOperators ComplexConjugate

noncomputable section

universe u

variable {G : Type u} {C P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype C] [Fintype P] [Fintype Q]

/-- A collar endpoint coordinate regarded as a positive-half observable.
It ignores the crossing variables and reads only the selected part of the
side configuration. -/
def splitEndpointPositiveObservable
    (selected : P → Prop) [DecidablePred selected]
    {I : Type*} (Phi : I → C((CollarCoordinate selected → G), ℂ)) (i : I) :
    LinkReflection.WilsonActionDecomposition.PositiveObservable G C P where
  toFun W := Phi i
    (splitSideMeasurableEquiv (G := G) selected W.2).1
  continuous_toFun :=
    (Phi i).continuous.comp <|
      (continuous_splitSide (G := G) selected).fst.comp continuous_snd

@[simp]
theorem splitEndpointPositiveObservable_apply
    (selected : P → Prop) [DecidablePred selected]
    {I : Type*} (Phi : I → C((CollarCoordinate selected → G), ℂ)) (i : I)
    (W : LinkReflection.HalfConfiguration G C P) :
    splitEndpointPositiveObservable (C := C) selected Phi i W =
      Phi i (splitSideMeasurableEquiv (G := G) selected W.2).1 :=
  rfl

/-- Gauge-fixed family pairings depend only on the identity-crossing slice
of each positive observable. -/
theorem familyGaugeFixedPairing_congr_fixedSlice
    (D : WilsonActionDecomposition G n C P Q)
    {I : Type*} [Fintype I] (beta : ℝ)
    (F H : I → LinkReflection.WilsonActionDecomposition.PositiveObservable G C P)
    (h : ∀ i U, F i (1, U) = H i (1, U)) :
    D.familyGaugeFixedPairing beta F F =
      D.familyGaugeFixedPairing beta H H := by
  unfold WilsonActionDecomposition.familyGaugeFixedPairing
  apply Finset.sum_congr rfl
  intro i _hi
  unfold WilsonActionDecomposition.gaugeFixedPairing
  apply integral_congr_ae
  filter_upwards with W
  rw [h i W.1, h i W.2]

/-- The actual positive-side Boltzmann factor, expressed in split
endpoint/remote coordinates. -/
def splitPositiveBoltzmannWeight
    (D : WilsonActionDecomposition G n C P Q)
    (selected : P → Prop) [DecidablePred selected] (beta : ℝ) :
    C(((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)), ℝ) where
  toFun ur := Real.exp (beta * D.positiveAction
    ((splitSideMeasurableEquiv (G := G) selected).symm ur))
  continuous_toFun := Real.continuous_exp.comp <|
    continuous_const.mul <| D.positiveAction.continuous.comp
      (continuous_mergeSide (G := G) selected)

@[simp]
theorem splitPositiveBoltzmannWeight_apply
    (D : WilsonActionDecomposition G n C P Q)
    (selected : P → Prop) [DecidablePred selected] (beta : ℝ)
    (ur : (CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) :
    splitPositiveBoltzmannWeight D selected beta ur =
      Real.exp (beta * D.positiveAction
        ((splitSideMeasurableEquiv (G := G) selected).symm ur)) :=
  rfl

theorem splitPositiveBoltzmannWeight_pos
    (D : WilsonActionDecomposition G n C P Q)
    (selected : P → Prop) [DecidablePred selected] (beta : ℝ)
    (ur : (CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) :
    0 < splitPositiveBoltzmannWeight D selected beta ur :=
  Real.exp_pos _

/-- Exact conversion of the crossing Wilson Boltzmann factor to the doubled
feature exponential.  The factor `2 * n` comes from the repository's
normalized Wilson character convention. -/
theorem exp_crossingAction_eq_expFeatureKernel
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    (beta : ℝ) (U V : SideConfiguration G P) :
    (Real.exp (beta * ∑ q : Q, D.representation.wilsonPotential
      (D.crossHolonomy q V * (D.crossHolonomy q U)⁻¹)) : ℂ) =
      expFeatureKernel (beta / (2 * n))
        (boundaryFeature (data.endpointFeature selected)
          (data.remoteFeature selected))
        ((splitSideMeasurableEquiv (G := G) selected U),
          (splitSideMeasurableEquiv (G := G) selected V)) := by
  rw [Complex.ofReal_exp, expFeatureKernel_apply]
  apply congrArg Complex.exp
  have hsum := D.sum_wilsonPotential_eq_crossKernel (U, V)
  have hkernel : D.crossKernel (U, V) =
      featureKernel
        (boundaryFeature (data.endpointFeature selected)
          (data.remoteFeature selected))
        ((splitSideMeasurableEquiv (G := G) selected U),
          (splitSideMeasurableEquiv (G := G) selected V)) := by
    rw [data.crossKernel_eq_endpoint_add_remote selected U V]
    exact (featureKernel_boundaryFeature_apply
      (data.endpointFeature selected) (data.remoteFeature selected)
      ((splitSideMeasurableEquiv (G := G) selected U),
        (splitSideMeasurableEquiv (G := G) selected V))).symm
  rw [← hkernel]
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast D.representation.dimension_pos.ne'
  push_cast at hsum ⊢
  rw [hsum]
  field_simp

/-- Exact gauge-fixed partition pairing after the endpoint/remote Haar
reindexing.  Both sides use normalized product Haar, so the identity has no
hidden gauge-volume factor. -/
theorem gaugeFixedPairing_one_eq_splitPartition
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    (beta : ℝ) :
    D.gaugeFixedPairing beta 1 1 =
      gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n)) (data.endpointFeature selected)
        (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) := by
  let e := splitSideMeasurableEquiv (G := G) selected
  let epair := MeasurableEquiv.prodCongr e e
  let muE := ProductHaar.measure G (CollarCoordinate selected)
  let muR := ProductHaar.measure G (RemoteCoordinate selected)
  let target :
      (((CollarCoordinate selected → G) ×
        (RemoteCoordinate selected → G)) ×
       ((CollarCoordinate selected → G) ×
        (RemoteCoordinate selected → G))) → ℂ := fun z ↦
    featureSideFactor
        (complexHalfWeight (splitPositiveBoltzmannWeight D selected beta))
        (complexHalfWeight (splitPositiveBoltzmannWeight D selected beta)) z *
      expFeatureKernel (beta / (2 * n))
        (boundaryFeature (data.endpointFeature selected)
          (data.remoteFeature selected)) z
  have hsplit := measurePreserving_splitSide (G := G) selected
  have hpair : MeasurePreserving epair
      ((ProductHaar.measure G P).prod (ProductHaar.measure G P))
      ((muE.prod muR).prod (muE.prod muR)) := by
    exact hsplit.prod hsplit
  have hpoint (U V : SideConfiguration G P) :
      (Real.exp (beta * D.gaugeFixedAction (U, V)) : ℂ) =
        target (epair (U, V)) := by
    rw [show D.gaugeFixedAction (U, V) =
        D.positiveAction U + D.positiveAction V +
          ∑ q : Q, D.representation.wilsonPotential
            (D.crossHolonomy q V * (D.crossHolonomy q U)⁻¹) by rfl]
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    rw [exp_crossingAction_eq_expFeatureKernel data selected beta U V]
    change _ = target (e U, e V)
    simp only [target, e,
      featureSideFactor_apply, complexHalfWeight_apply,
      splitPositiveBoltzmannWeight_apply,
      Complex.conj_ofReal]
    rw [(splitSideMeasurableEquiv (G := G) selected).symm_apply_apply U,
      (splitSideMeasurableEquiv (G := G) selected).symm_apply_apply V]
  calc
    D.gaugeFixedPairing beta 1 1 =
        ∫ W : SideConfiguration G P × SideConfiguration G P,
          target (epair W)
          ∂(ProductHaar.measure G P).prod (ProductHaar.measure G P) := by
      unfold WilsonActionDecomposition.gaugeFixedPairing
      apply integral_congr_ae
      filter_upwards with W
      simpa only [ContinuousMap.one_apply, map_one, mul_one] using
        hpoint W.1 W.2
    _ = ∫ z, target z ∂(muE.prod muR).prod (muE.prod muR) :=
      hpair.integral_comp' target
    _ = gaugeFixedPartitionPairing muE muR (beta / (2 * n))
        (data.endpointFeature selected) (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) := rfl

/-- Exact vector numerator identity for the collar endpoint family.  This is
the numerator analogue of `gaugeFixedPairing_one_eq_splitPartition`; the
same coordinate change and the same positive-side Boltzmann factor occur on
both sides, hence there is no relative normalization constant. -/
theorem familyGaugeFixedPairing_splitEndpoint_eq_numerator
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    {I : Type*} [Fintype I]
    (beta : ℝ) (Phi : I → C((CollarCoordinate selected → G), ℂ)) :
    D.familyGaugeFixedPairing beta
        (splitEndpointPositiveObservable (C := C) selected Phi)
        (splitEndpointPositiveObservable (C := C) selected Phi) =
      gaugeFixedEndpointNumerator
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n)) (data.endpointFeature selected)
        (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) Phi := by
  let e := splitSideMeasurableEquiv (G := G) selected
  let epair := MeasurableEquiv.prodCongr e e
  let muE := ProductHaar.measure G (CollarCoordinate selected)
  let muR := ProductHaar.measure G (RemoteCoordinate selected)
  let F := splitPositiveBoltzmannWeight D selected beta
  let target :
      (((CollarCoordinate selected → G) ×
        (RemoteCoordinate selected → G)) ×
       ((CollarCoordinate selected → G) ×
        (RemoteCoordinate selected → G))) → ℂ := fun z ↦
    familyFeatureSideFactor (weightedEndpointCoordinate F Phi)
        (weightedEndpointCoordinate F Phi) z *
      expFeatureKernel (beta / (2 * n))
        (boundaryFeature (data.endpointFeature selected)
          (data.remoteFeature selected)) z
  have hsplit := measurePreserving_splitSide (G := G) selected
  have hpair : MeasurePreserving epair
      ((ProductHaar.measure G P).prod (ProductHaar.measure G P))
      ((muE.prod muR).prod (muE.prod muR)) := by
    exact hsplit.prod hsplit
  have hpoint (U V : SideConfiguration G P) :
      (Real.exp (beta * D.gaugeFixedAction (U, V)) : ℂ) *
          ∑ i, star
              (splitEndpointPositiveObservable (C := C) selected Phi i (1, U)) *
            splitEndpointPositiveObservable (C := C) selected Phi i (1, V) =
        target (epair (U, V)) := by
    rw [show D.gaugeFixedAction (U, V) =
        D.positiveAction U + D.positiveAction V +
          ∑ q : Q, D.representation.wilsonPotential
            (D.crossHolonomy q V * (D.crossHolonomy q U)⁻¹) by rfl]
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    rw [exp_crossingAction_eq_expFeatureKernel data selected beta U V]
    change _ = target (e U, e V)
    simp only [target, F, e, familyFeatureSideFactor_apply,
      weightedEndpointCoordinate_apply, splitEndpointPositiveObservable_apply,
      splitPositiveBoltzmannWeight_apply, map_mul, Complex.conj_ofReal,
      Complex.ofReal_mul]
    rw [(splitSideMeasurableEquiv (G := G) selected).symm_apply_apply U,
      (splitSideMeasurableEquiv (G := G) selected).symm_apply_apply V]
    push_cast
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [starRingEnd_apply]
    ring
  calc
    D.familyGaugeFixedPairing beta
        (splitEndpointPositiveObservable (C := C) selected Phi)
        (splitEndpointPositiveObservable (C := C) selected Phi) =
        ∫ W : SideConfiguration G P × SideConfiguration G P,
          target (epair W)
          ∂(ProductHaar.measure G P).prod (ProductHaar.measure G P) := by
      unfold WilsonActionDecomposition.familyGaugeFixedPairing
        WilsonActionDecomposition.gaugeFixedPairing
      rw [← MeasureTheory.integral_finsetSum Finset.univ]
      · apply integral_congr_ae
        filter_upwards with W
        rw [← hpoint W.1 W.2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [starRingEnd_apply]
        ring
      · intro i _hi
        exact D.integrable_gaugeFixedPairingIntegrand beta
          (splitEndpointPositiveObservable (C := C) selected Phi i)
          (splitEndpointPositiveObservable (C := C) selected Phi i)
    _ = ∫ z, target z ∂(muE.prod muR).prod (muE.prod muR) :=
      hpair.integral_comp' target
    _ = gaugeFixedEndpointNumerator muE muR (beta / (2 * n))
        (data.endpointFeature selected) (data.remoteFeature selected)
        F Phi := rfl

end

end YangMills.Gluelump.OneLink
