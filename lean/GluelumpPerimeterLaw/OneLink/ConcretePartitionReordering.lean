/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteGaugeFixedFactorization
import GluelumpPerimeterLaw.OneLink.UniformPositivity

/-!
# Exact real reordering of the gauge-fixed partition pairing

The scalar gauge-fixed pairing is initially integrated in the order
`((u, r), (v, s))`, with one endpoint/remote pair for each reflected half.
The finite-energy cancellation argument instead uses the order
`((r, s), (u, v))`, with the remote pair outermost.  This file implements
that coordinate permutation as a measurable equivalence, proves that it
preserves the corresponding product measures, and performs the reordering
without a normalization constant.

For the doubled Wilson crossing features, both exponential kernels are
exactly real.  Consequently the complex gauge-fixed partition pairing is
the complexification of `reorderedSplitPartition`; in particular, its real
part is the reordered partition and its imaginary part vanishes.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Gauge.LinkReflection

noncomputable section

universe uE uR vE vR u

/-! ## The endpoint/remote coordinate permutation -/

section ReorderingEquiv

variable {UE : Type uE} {UR : Type uR}
  [MeasurableSpace UE] [MeasurableSpace UR]

/-- The permutation
`((u, r), (v, s)) |-> ((r, s), (u, v))` as a measurable equivalence. -/
def boundaryPairReorder :
    ((UE × UR) × (UE × UR)) ≃ᵐ ((UR × UR) × (UE × UE)) :=
  let inner : UR × (UE × UR) ≃ᵐ UE × (UR × UR) :=
    MeasurableEquiv.prodAssoc.symm |>.trans
      ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl UR)).trans MeasurableEquiv.prodAssoc)
  MeasurableEquiv.prodAssoc |>.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl UE) inner).trans
      (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm))

@[simp]
theorem boundaryPairReorder_apply (z : (UE × UR) × (UE × UR)) :
    boundaryPairReorder z = ((z.1.2, z.2.2), (z.1.1, z.2.1)) := by
  rfl

/-- The endpoint/remote permutation preserves the fourfold product measure.
This is assembled only from Mathlib's product associativity and swap maps. -/
theorem measurePreserving_boundaryPairReorder
    (muE : Measure UE) (muR : Measure UR)
    [SFinite muE] [SFinite muR] :
    MeasurePreserving (boundaryPairReorder (UE := UE) (UR := UR))
      ((muE.prod muR).prod (muE.prod muR))
      ((muR.prod muR).prod (muE.prod muE)) := by
  let hAssoc :=
    MeasureTheory.measurePreserving_prodAssoc muE muR (muE.prod muR)
  let hInnerAssocInv := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (MeasureTheory.measurePreserving_prodAssoc muR muE muR)
  let hInnerSwap : MeasurePreserving
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl UR))
      ((muR.prod muE).prod muR) ((muE.prod muR).prod muR) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id muR)
  let hInnerAssoc :=
    MeasureTheory.measurePreserving_prodAssoc muE muR muR
  let hInner := hInnerAssoc.comp (hInnerSwap.comp hInnerAssocInv)
  let hOuter := (MeasurePreserving.id muE).prod hInner
  let hOuterAssocInv := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (MeasureTheory.measurePreserving_prodAssoc muE muE (muR.prod muR))
  let hFinalSwap : MeasurePreserving
      (MeasurableEquiv.prodComm : (UE × UE) × (UR × UR) ≃ᵐ
        (UR × UR) × (UE × UE))
      ((muE.prod muE).prod (muR.prod muR))
      ((muR.prod muR).prod (muE.prod muE)) :=
    Measure.measurePreserving_swap
  simpa only [boundaryPairReorder, Function.comp_def] using
    hFinalSwap.comp (hOuterAssocInv.comp (hOuter.comp hAssoc))

end ReorderingEquiv

/-! ## Reordering a real split kernel -/

section RealKernel

variable {UE : Type uE} {UR : Type uR} {AE : Type vE} {AR : Type vR}
  [TopologicalSpace UE] [CompactSpace UE]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [TopologicalSpace UR] [CompactSpace UR]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  [Fintype AE] [Fintype AR]

/-- A gauge-fixed partition pairing whose two split exponential kernels are
real is exactly the complexification of the remote-first reordered
partition. -/
theorem gaugeFixedPartitionPairing_eq_reorderedSplitPartition_of_real
    (muE : Measure UE) (muR : Measure UR)
    [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ))
    (KE : C(UE × UE, ℝ)) (KR : C(UR × UR, ℝ))
    (F : C(UE × UR, ℝ))
    (hE : ∀ z, expFeatureKernel alpha featureE z = (KE z : ℂ))
    (hR : ∀ z, expFeatureKernel alpha featureR z = (KR z : ℂ)) :
    gaugeFixedPartitionPairing muE muR alpha featureE featureR F =
      (reorderedSplitPartition muE muR KE KR F : ℂ) := by
  let e := boundaryPairReorder (UE := UE) (UR := UR)
  let target : (UR × UR) × (UE × UE) → ℝ := fun z ↦
    F (z.2.1, z.1.1) * F (z.2.2, z.1.2) * KE z.2 * KR z.1
  have he : MeasurePreserving e
      ((muE.prod muR).prod (muE.prod muR))
      ((muR.prod muR).prod (muE.prod muE)) :=
    measurePreserving_boundaryPairReorder muE muR
  calc
    gaugeFixedPartitionPairing muE muR alpha featureE featureR F =
        ∫ z : (UE × UR) × (UE × UR), (target (e z) : ℂ)
          ∂(muE.prod muR).prod (muE.prod muR) := by
      unfold gaugeFixedPartitionPairing boundaryMeasure
      apply integral_congr_ae
      filter_upwards with z
      rw [expFeatureKernel_boundaryFeature_apply, hE, hR]
      simp only [featureSideFactor_apply, complexHalfWeight_apply,
        Complex.conj_ofReal, e, target, boundaryPairReorder_apply]
      push_cast
      ring
    _ = ((∫ z : (UE × UR) × (UE × UR), target (e z)
          ∂(muE.prod muR).prod (muE.prod muR)) : ℂ) := by
      rw [integral_complex_ofReal]
    _ = ((∫ z : (UR × UR) × (UE × UE), target z
          ∂(muR.prod muR).prod (muE.prod muE)) : ℂ) := by
      exact he.integral_comp e.measurableEmbedding (fun z ↦ (target z : ℂ))
    _ = (reorderedSplitPartition muE muR KE KR F : ℂ) := by
      rw [integral_complex_ofReal]
      rfl

end RealKernel

/-! ## Doubled Wilson crossing features -/

section CoordinateCrossing

variable {G : Type u} {C P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q]

/-- For the concrete doubled crossing features, the entire scalar pairing is
the complexification of the real remote-first partition. -/
theorem gaugeFixedPartitionPairing_eq_reorderedSplitPartition
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    (alpha : ℝ)
    (F : C(((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)), ℝ)) :
    gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        alpha (data.endpointFeature selected) (data.remoteFeature selected) F =
      (reorderedSplitPartition
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (realExpFeatureKernel alpha (data.endpointFeature selected))
        (realExpFeatureKernel alpha (data.remoteFeature selected)) F : ℂ) :=
  gaugeFixedPartitionPairing_eq_reorderedSplitPartition_of_real
    (ProductHaar.measure G (CollarCoordinate selected))
    (ProductHaar.measure G (RemoteCoordinate selected)) alpha
    (data.endpointFeature selected) (data.remoteFeature selected)
    (realExpFeatureKernel alpha (data.endpointFeature selected))
    (realExpFeatureKernel alpha (data.remoteFeature selected)) F
    (data.expFeatureKernel_endpointFeature_eq_real selected alpha)
    (data.expFeatureKernel_remoteFeature_eq_real selected alpha)

/-- The real part of the concrete gauge-fixed partition pairing is exactly
the reordered real partition used by the cancellation estimate. -/
theorem re_gaugeFixedPartitionPairing_eq_reorderedSplitPartition
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    (alpha : ℝ)
    (F : C(((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)), ℝ)) :
    (gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        alpha (data.endpointFeature selected)
          (data.remoteFeature selected) F).re =
      reorderedSplitPartition
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (realExpFeatureKernel alpha (data.endpointFeature selected))
        (realExpFeatureKernel alpha (data.remoteFeature selected)) F := by
  rw [gaugeFixedPartitionPairing_eq_reorderedSplitPartition data selected alpha F]
  simp

/-- The imaginary part of the concrete gauge-fixed partition pairing
vanishes exactly. -/
theorem im_gaugeFixedPartitionPairing_eq_zero
    {D : WilsonActionDecomposition G n C P Q}
    (data : CoordinateCrossingData D)
    (selected : P → Prop) [DecidablePred selected]
    (alpha : ℝ)
    (F : C(((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)), ℝ)) :
    (gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        alpha (data.endpointFeature selected)
          (data.remoteFeature selected) F).im = 0 := by
  rw [gaugeFixedPartitionPairing_eq_reorderedSplitPartition data selected alpha F]
  simp

end CoordinateCrossing

end

end YangMills.Gluelump.OneLink
