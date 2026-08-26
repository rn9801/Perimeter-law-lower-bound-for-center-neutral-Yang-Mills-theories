/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.EndpointPolynomial

/-!
# Exact endpoint/remote factorization of a gauge-fixed bond kernel

After crossing-link gauge fixing, the variables visible to crossing
plaquettes split into a fixed endpoint collar and a volume-dependent remote
boundary.  This file records the exact analytic factorization for that split.
It is deliberately independent of a particular lattice box: the concrete
adapter only has to identify its boundary coordinates with `UE × UR`.

There are no discarded normalization constants.  Both the scalar partition
pairing and the vector endpoint numerator are defined using the same
exponential kernel and the same half-box weight.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

universe uE uR vE vR w

variable {UE : Type uE} {UR : Type uR}
  {AE : Type vE} {AR : Type vR} {I : Type w}
  [TopologicalSpace UE] [TopologicalSpace UR]
  [Fintype AE] [Fintype AR] [Fintype I]

/-- Pull an endpoint feature back to the full boundary space. -/
def endpointFeatureLift (featureE : AE → C(UE, ℂ)) (a : AE) :
    C(UE × UR, ℂ) :=
  (featureE a).comp ContinuousMap.fst

/-- Pull a remote feature back to the full boundary space. -/
def remoteFeatureLift (featureR : AR → C(UR, ℂ)) (a : AR) :
    C(UE × UR, ℂ) :=
  (featureR a).comp ContinuousMap.snd

/-- The disjoint endpoint/remote feature family on a half-boundary. -/
def boundaryFeature
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ)) :
    AE ⊕ AR → C(UE × UR, ℂ) :=
  sumFeature (endpointFeatureLift featureE) (remoteFeatureLift featureR)

@[simp]
theorem endpointFeatureLift_apply
    (featureE : AE → C(UE, ℂ)) (a : AE) (u : UE × UR) :
    endpointFeatureLift featureE a u = featureE a u.1 :=
  rfl

@[simp]
theorem remoteFeatureLift_apply
    (featureR : AR → C(UR, ℂ)) (a : AR) (u : UE × UR) :
    remoteFeatureLift featureR a u = featureR a u.2 :=
  rfl

/-- Exact additivity of the boundary rank-one kernel. -/
theorem featureKernel_boundaryFeature_apply
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (z : (UE × UR) × (UE × UR)) :
    featureKernel (boundaryFeature featureE featureR) z =
      featureKernel featureE (z.1.1, z.2.1) +
        featureKernel featureR (z.1.2, z.2.2) := by
  simp [boundaryFeature, featureKernel_apply, sumFeature,
    endpointFeatureLift, remoteFeatureLift, Fintype.sum_sum_type]

/-- Exact factorization of the crossing exponential into the fixed endpoint
kernel and the remote kernel. -/
theorem expFeatureKernel_boundaryFeature_apply
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ))
    (z : (UE × UR) × (UE × UR)) :
    expFeatureKernel alpha (boundaryFeature featureE featureR) z =
      expFeatureKernel alpha featureE (z.1.1, z.2.1) *
        expFeatureKernel alpha featureR (z.1.2, z.2.2) := by
  rw [expFeatureKernel_apply, featureKernel_boundaryFeature_apply,
    mul_add, Complex.exp_add]
  rfl

/-- Regard a real half-box weight as a complex continuous function. -/
def complexHalfWeight (F : C(UE × UR, ℝ)) : C(UE × UR, ℂ) where
  toFun u := (F u : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp F.continuous

@[simp]
theorem complexHalfWeight_apply (F : C(UE × UR, ℝ)) (u : UE × UR) :
    complexHalfWeight F u = (F u : ℂ) :=
  rfl

/-- Multiply an endpoint coordinate by the common half-box weight. -/
def weightedEndpointCoordinate
    (F : C(UE × UR, ℝ)) (Phi : I → C(UE, ℂ)) (i : I) :
    C(UE × UR, ℂ) :=
  complexHalfWeight F * (Phi i).comp ContinuousMap.fst

@[simp]
theorem weightedEndpointCoordinate_apply
    (F : C(UE × UR, ℝ)) (Phi : I → C(UE, ℂ))
    (i : I) (u : UE × UR) :
    weightedEndpointCoordinate F Phi i u = (F u : ℂ) * Phi i u.1 :=
  rfl

section Pairings

variable [CompactSpace UE] [CompactSpace UR]
  [MeasurableSpace UE] [BorelSpace UE] [SecondCountableTopology UE]
  [MeasurableSpace UR] [BorelSpace UR] [SecondCountableTopology UR]
  (muE : Measure UE) (muR : Measure UR)
  [IsProbabilityMeasure muE] [IsProbabilityMeasure muR]

/-- Product Haar/probability measure on one gauge-fixed half-boundary. -/
abbrev boundaryMeasure : Measure (UE × UR) := muE.prod muR

/-- The exact scalar gauge-fixed partition pairing. -/
def gaugeFixedPartitionPairing
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (F : C(UE × UR, ℝ)) : ℂ :=
  ∫ z : (UE × UR) × (UE × UR),
    featureSideFactor (complexHalfWeight F) (complexHalfWeight F) z *
      expFeatureKernel alpha (boundaryFeature featureE featureR) z
    ∂(boundaryMeasure muE muR).prod (boundaryMeasure muE muR)

/-- The exact vector-valued one-link numerator after the distinguished
crossing transporter has been fixed to the identity. -/
def gaugeFixedEndpointNumerator
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (F : C(UE × UR, ℝ))
    (Phi : I → C(UE, ℂ)) : ℂ :=
  ∫ z : (UE × UR) × (UE × UR),
    familyFeatureSideFactor (weightedEndpointCoordinate F Phi)
      (weightedEndpointCoordinate F Phi) z *
      expFeatureKernel alpha (boundaryFeature featureE featureR) z
    ∂(boundaryMeasure muE muR).prod (boundaryMeasure muE muR)

/-- Pointwise form of the numerator integrand: endpoint Hermitian pairing,
two half-box weights, and the exactly split endpoint/remote kernels. -/
theorem gaugeFixedEndpointNumerator_eq_splitKernel
    (alpha : ℝ) (featureE : AE → C(UE, ℂ))
    (featureR : AR → C(UR, ℂ)) (F : C(UE × UR, ℝ))
    (Phi : I → C(UE, ℂ)) :
    gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi =
      ∫ z : (UE × UR) × (UE × UR),
        ((F z.1 * F z.2 : ℝ) : ℂ) *
          (∑ i, conj (Phi i z.1.1) * Phi i z.2.1) *
          expFeatureKernel alpha featureE (z.1.1, z.2.1) *
          expFeatureKernel alpha featureR (z.1.2, z.2.2)
        ∂(boundaryMeasure muE muR).prod (boundaryMeasure muE muR) := by
  apply integral_congr_ae
  filter_upwards with z
  have hsum :
      (∑ i, conj (((F z.1 : ℝ) : ℂ) * Phi i z.1.1) *
        (((F z.2 : ℝ) : ℂ) * Phi i z.2.1)) =
      (((F z.1 * F z.2 : ℝ) : ℂ) *
        ∑ i, conj (Phi i z.1.1) * Phi i z.2.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [expFeatureKernel_boundaryFeature_apply]
  simp only [familyFeatureSideFactor_apply, weightedEndpointCoordinate_apply]
  rw [hsum]
  ring

/-- At nonnegative coupling the exact vector numerator is real and
nonnegative, directly from the finite-coordinate exponential Gram theorem. -/
theorem gaugeFixedEndpointNumerator_nonneg
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (featureE : AE → C(UE, ℂ)) (featureR : AR → C(UR, ℂ))
    (F : C(UE × UR, ℝ)) (Phi : I → C(UE, ℂ)) :
    Complex.im
        (gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi) = 0 ∧
      0 ≤ Complex.re
        (gaugeFixedEndpointNumerator muE muR alpha featureE featureR F Phi) := by
  exact familyExpFeatureKernel_pairing_self_nonneg
    (boundaryMeasure muE muR) halpha
    (boundaryFeature featureE featureR)
    (weightedEndpointCoordinate F Phi)

end Pairings

end

end YangMills.Gluelump.OneLink
