/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraight
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixed

/-!
# Completed-box crossing certificates for physical straight lines

This adapter certifies the odd, link-centered members of the neutral physical
straight-line family for the completed free-boundary exhaustion.  Keeping
these certificates here leaves the pointwise geometry and abstract
reflection-positivity propagation independent of the strong-coupling limit
construction.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

theorem conjSpanLinkStraight_eventuallyFamilyNormSquare
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    StrongCoupling.EventuallyLinkCrossingFamilyNormSquare (ι := Fin r)
      (Geometry.armAxis hd)
      (conjSpanLinkStraightObservable hd sigma rho T z hz l) := by
  let a := Geometry.armAxis hd
  let Phi := conjSpanLinkStraightEndpoint hd sigma rho T z l
  exact eventuallyLinkCrossingFamilyNormSquare_reflectedFullPath_of_support
    rho Phi a z hz (straightPositiveHalfPath a z l)
    (conjSpanLinkStraightEndpoint_covariant hd sigma rho T z l)
    (conjSpanLinkStraightEndpoint_supportedInLinkPositiveHalf
      hd sigma rho T z hz l)
    (straightPositiveHalfPath_supportedInLinkPositiveHalf a 0 z hz l)

theorem conjSpanLinkStraight_eventuallyFamilyCauchySchwarz
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l s : ℕ) :
    StrongCoupling.EventuallyLinkCrossingFamilyCauchySchwarz (ι := Fin r)
      (Geometry.armAxis hd)
      (conjSpanLinkStraightMixedObservable hd sigma rho T z hz l s)
      (conjSpanLinkStraightObservable hd sigma rho T z hz l)
      (conjSpanLinkStraightObservable hd sigma rho T z hz s) := by
  let a := Geometry.armAxis hd
  let Phi := conjSpanLinkStraightEndpoint hd sigma rho T z l
  let Psi := conjSpanLinkStraightEndpoint hd sigma rho T z s
  exact eventuallyLinkCrossingFamilyCauchySchwarz_reflectedMixed_of_support
    rho Phi Psi a z hz
    (straightPositiveHalfPath a z l) (straightPositiveHalfPath a z s)
    (conjSpanLinkStraightEndpoint_covariant hd sigma rho T z l)
    (conjSpanLinkStraightEndpoint_covariant hd sigma rho T z s)
    (conjSpanLinkStraightEndpoint_supportedInLinkPositiveHalf
      hd sigma rho T z hz l)
    (conjSpanLinkStraightEndpoint_supportedInLinkPositiveHalf
      hd sigma rho T z hz s)
    (straightPositiveHalfPath_supportedInLinkPositiveHalf a 0 z hz l)
    (straightPositiveHalfPath_supportedInLinkPositiveHalf a 0 z hz s)

end

end YangMills.Gluelump.Propagation
