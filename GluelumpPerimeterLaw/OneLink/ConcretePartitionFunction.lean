/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcretePartitionReordering
import GluelumpPerimeterLaw.OneLink.CrossFeatureSplit

/-!
# The physical finite-volume partition function in split coordinates

This file specializes the concrete link-reflection gauge-fixing identity to
the constant-one local observable.  It first identifies the physical Wilson
partition function with the scalar gauge-fixed pairing, then composes that
identity with the exact endpoint/remote split and real coordinate reordering.
All measures are normalized product Haar measures, so no gauge-volume or
coordinate-change factor occurs.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson
open Gauge.LinkReflection

noncomputable section

universe u

variable {d n : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The physical Wilson partition function is exactly the constant-one
gauge-fixed link-reflection pairing. -/
theorem partitionFunction_eq_linkGaugeFixedPairing
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (rho : ContinuousUnitaryRepData G n) (beta : ℝ) :
    (FiniteVolume.partitionFunction Lambda rho.wilsonPotential beta : ℂ) =
      (Lambda.linkWilsonDecomposition tau k hLambda rho).gaugeFixedPairing
        beta 1 1 := by
  let F : LocalObservable d G := LocalObservable.const 1
  have hhalf : F.SupportedInLinkPositiveHalf tau k := by
    intro e he
    simp [F, LocalObservable.const] at he
  have hgauge : Gauge.IsGaugeInvariant F := by
    intro g A
    rfl
  have hdyn : F.support ⊆ Lambda.dynamicEdges := by
    intro e he
    simp [F, LocalObservable.const] at he
  have h := Lambda.integral_haar_linkReflectionProduct_eq_gaugeFixed
    tau k hLambda hclosed rho beta F F hhalf hhalf hgauge hgauge hdyn hdyn
  have hrestrict : Lambda.linkRestrictObservable tau k hLambda F = 1 := by
    ext W
    rfl
  calc
    (FiniteVolume.partitionFunction Lambda rho.wilsonPotential beta : ℂ) =
        ∫ V, (Real.exp (beta * FiniteVolume.action Lambda
          rho.wilsonPotential V) : ℂ) ∂Lambda.haarMeasure := by
      rw [integral_complex_ofReal]
      rfl
    _ = ∫ V, (Real.exp (beta * FiniteVolume.action Lambda
          rho.wilsonPotential V) : ℂ) *
          F.linkReflectionProduct tau k F (Lambda.evaluate V)
          ∂Lambda.haarMeasure := by
      apply integral_congr_ae
      filter_upwards with V
      change _ = _ * (star (1 : ℂ) * 1)
      norm_num
    _ = (Lambda.linkWilsonDecomposition tau k hLambda rho).gaugeFixedPairing
        beta (Lambda.linkRestrictObservable tau k hLambda F)
          (Lambda.linkRestrictObservable tau k hLambda F) := h
    _ = (Lambda.linkWilsonDecomposition tau k hLambda rho).gaugeFixedPairing
        beta 1 1 := by rw [hrestrict]

/-- The physical Wilson partition function is the real remote-first split
partition used by the all-coupling cancellation theorem. -/
theorem partitionFunction_eq_reorderedSplitPartition
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (rho : ContinuousUnitaryRepData G n)
    (selected : Lambda.linkPositiveEdges tau k → Prop)
    [DecidablePred selected] (beta : ℝ) :
    FiniteVolume.partitionFunction Lambda rho.wilsonPotential beta =
      reorderedSplitPartition
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (realExpFeatureKernel (beta / (2 * n))
          ((FiniteSpecification.linkCoordinateCrossingData
            Lambda tau k hLambda hclosed rho).endpointFeature selected))
        (realExpFeatureKernel (beta / (2 * n))
          ((FiniteSpecification.linkCoordinateCrossingData
            Lambda tau k hLambda hclosed rho).remoteFeature selected))
        (splitPositiveBoltzmannWeight
          (Lambda.linkWilsonDecomposition tau k hLambda rho) selected beta) := by
  let D := Lambda.linkWilsonDecomposition tau k hLambda rho
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed rho
  have hZ :
      (FiniteVolume.partitionFunction Lambda rho.wilsonPotential beta : ℂ) =
        D.gaugeFixedPairing beta 1 1 :=
    partitionFunction_eq_linkGaugeFixedPairing
      Lambda tau k hLambda hclosed rho beta
  have hsplit : D.gaugeFixedPairing beta 1 1 =
      gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n)) (data.endpointFeature selected)
        (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) :=
    gaugeFixedPairing_one_eq_splitPartition data selected beta
  have hreorder := gaugeFixedPartitionPairing_eq_reorderedSplitPartition
    data selected (beta / (2 * n))
      (splitPositiveBoltzmannWeight D selected beta)
  apply Complex.ofReal_injective
  calc
    (FiniteVolume.partitionFunction Lambda rho.wilsonPotential beta : ℂ) =
        D.gaugeFixedPairing beta 1 1 := hZ
    _ = gaugeFixedPartitionPairing
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n)) (data.endpointFeature selected)
        (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) := hsplit
    _ = (reorderedSplitPartition
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (realExpFeatureKernel (beta / (2 * n))
          (data.endpointFeature selected))
        (realExpFeatureKernel (beta / (2 * n))
          (data.remoteFeature selected))
        (splitPositiveBoltzmannWeight D selected beta) : ℂ) := hreorder

end

end YangMills.Gluelump.OneLink
