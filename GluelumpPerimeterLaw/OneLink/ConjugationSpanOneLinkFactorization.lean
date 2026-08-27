/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteFiniteEnergy
import GluelumpPerimeterLaw.OneLink.ConjugationSpanOneLinkObservableCore
import GluelumpPerimeterLaw.OneLink.FiniteVolumePositivity

/-!
# Gauge-fixed factorization of the direct conjugation-span one-link seed

The positive endpoint is the canonical direct endpoint based at the first
site beyond the reflected bond.  Its literal link-reflected copy is used at
the negative endpoint, exactly as required by the existing crossing-family
reflection certificate.  On the identity-crossing slice the half family is
the selected collar coordinate family constructed in
`ConjugationSpanBoundaryMode`.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint Propagation
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The actual reflected half family agrees on the gauge-fixed slice with
the split direct collar family. -/
theorem conjSpanReflectedOneLinkHalfFamily_fixedSlice_eq_splitEndpoint
    (Lambda : FiniteSpecification d G)
    (hd : 3 ≤ d)
    (hLambda : Lambda.LinkSymmetric (Geometry.armAxis hd) 0)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hcollar : combEndpointCollar (m := m) hd
        (step z (.forward (Geometry.armAxis hd))) ⊆
      Lambda.linkPositiveEdges (Geometry.armAxis hd) 0)
    (i : Fin r)
    (U : Gauge.LinkReflection.SideConfiguration G
      (Lambda.linkPositiveEdges (Geometry.armAxis hd) 0)) :
    reflectedEndpointOneLinkHalfFamily Lambda (Geometry.armAxis hd) hLambda rho
        (conjSpanPhi hd sigma rho T
          (step z (.forward (Geometry.armAxis hd)))) z hz i (1, U) =
      splitEndpointPositiveObservable
        (C := Lambda.linkCrossingEdges (Geometry.armAxis hd) 0)
        (linkCombSelected (m := m) Lambda (Geometry.armAxis hd) 0 hd
          (step z (.forward (Geometry.armAxis hd))))
        (linkConjSpanPhiFamily Lambda (Geometry.armAxis hd) 0 hd sigma rho T
          (step z (.forward (Geometry.armAxis hd))) hcollar) i (1, U) := by
  let tau := Geometry.armAxis hd
  let y := step z (.forward tau)
  have hy : y tau = 1 := by
    simp [y, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hPsi : (conjSpanPhi hd sigma rho T y).SupportedInLinkPositiveHalf
      tau 0 := by
    intro e he
    rw [conjSpanPhi_support] at he
    have hp := basedLoopSupport_combLoops_armPlane hd y e he
    change 0 < e.target tau
    rw [hp.2, hy]
    omega
  rw [reflectedEndpointOneLinkHalfFamily_fixedSlice_eq_endpoint
    Lambda tau hLambda rho (conjSpanPhi hd sigma rho T y) z hz hPsi i U]
  exact (linkConjSpanPhiFamily_splitSide_eq
    Lambda tau 0 hLambda hd sigma rho T y hcollar i U).symm

/-- Exact equality between the concrete reflected half-family pairing and
the abstract split endpoint numerator. -/
theorem conjSpanReflectedOneLink_familyPairing_eq_numerator
    (Lambda : FiniteSpecification d G)
    (hd : 3 ≤ d)
    (hLambda : Lambda.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Lambda.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hcollar : combEndpointCollar (m := m) hd
        (step z (.forward (Geometry.armAxis hd))) ⊆
      Lambda.linkPositiveEdges (Geometry.armAxis hd) 0)
    (beta : ℝ) :
    let tau := Geometry.armAxis hd
    let y := step z (.forward tau)
    let D := Lambda.linkWilsonDecomposition tau 0 hLambda sigma
    let selected := linkCombSelected (m := m) Lambda tau 0 hd y
    D.familyGaugeFixedPairing beta
        (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho
          (conjSpanPhi hd sigma rho T y) z hz)
        (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho
          (conjSpanPhi hd sigma rho T y) z hz) =
      gaugeFixedEndpointNumerator
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n))
        ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau 0 hLambda hclosed sigma).endpointFeature selected)
        ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau 0 hLambda hclosed sigma).remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta)
        (linkConjSpanPhiFamily Lambda tau 0 hd sigma rho T y hcollar) := by
  let tau := Geometry.armAxis hd
  let y := step z (.forward tau)
  let D := Lambda.linkWilsonDecomposition tau 0 hLambda sigma
  let selected := linkCombSelected (m := m) Lambda tau 0 hd y
  let Phi := linkConjSpanPhiFamily Lambda tau 0 hd sigma rho T y hcollar
  let Factual := reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho
    (conjSpanPhi hd sigma rho T y) z hz
  let Fsplit := splitEndpointPositiveObservable
    (C := Lambda.linkCrossingEdges tau 0) selected Phi
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau 0 hLambda hclosed sigma
  calc
    D.familyGaugeFixedPairing beta Factual Factual =
        D.familyGaugeFixedPairing beta Fsplit Fsplit := by
      apply familyGaugeFixedPairing_congr_fixedSlice D beta
      intro i U
      exact conjSpanReflectedOneLinkHalfFamily_fixedSlice_eq_splitEndpoint
        Lambda hd hLambda sigma rho T z hz hcollar i U
    _ = gaugeFixedEndpointNumerator
        (ProductHaar.measure G (CollarCoordinate selected))
        (ProductHaar.measure G (RemoteCoordinate selected))
        (beta / (2 * n)) (data.endpointFeature selected)
        (data.remoteFeature selected)
        (splitPositiveBoltzmannWeight D selected beta) Phi :=
      familyGaugeFixedPairing_splitEndpoint_eq_numerator
        data selected beta Phi

end

end YangMills.Gluelump.OneLink
