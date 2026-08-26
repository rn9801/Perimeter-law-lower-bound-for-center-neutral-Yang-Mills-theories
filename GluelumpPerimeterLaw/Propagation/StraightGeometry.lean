/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.StraightGeometryCore
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixed

/-!
# Concrete straight screened-arm geometry

This file supplies the completed-box crossing certificates and the legacy
centered strong-coupling wrapper for the neutral straight geometry in
`StraightGeometryCore`.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson StrongCoupling
open Endpoint
open scoped Matrix

noncomputable section

variable {d m n N : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The explicit transverse axial endpoint on a straight arm supplies an
eventual Gram norm-square certificate in the infinite-volume link-symmetric
exhaustion. -/
theorem transverseStraightArm_eventuallyLinkCrossingFamilyNormSquare
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) :
    EventuallyLinkCrossingFamilyNormSquare (ι := Fin n)
      (Geometry.armAxis hd)
      (let y := Path.advance
          (step z (.forward (Geometry.armAxis hd)))
          (.forward (Geometry.armAxis hd)) length
       let Psi := transverseAxialEndpoint hd eta y T
       screenedObservable rho
         (Psi.linkPullback (Geometry.armAxis hd) 0) Psi
         (reflectedFullPath (Geometry.armAxis hd) 0 z hz
           (straightPositiveHalfPath (Geometry.armAxis hd) z length))) := by
  let τ := Geometry.armAxis hd
  let y := Path.advance (step z (.forward τ)) (.forward τ) length
  let Psi := transverseAxialEndpoint hd eta y T
  have hcoord : y τ = 0 + 1 + length := by
    exact straightPositiveHalfPath_target_coord τ 0 z hz length
  have hPsiCov : GaugeCovariantAt rho y Psi :=
    transverseAxialEndpoint_covariant hd rho eta y T hT
  have hPsiAt : Psi.SupportedInLinkPositiveHalf τ (y τ - 1) :=
    transverseAxialEndpoint_supportedInLinkPositiveHalf hd eta y T
  have hPsi : Psi.SupportedInLinkPositiveHalf τ 0 := by
    apply hPsiAt.mono
    rw [hcoord]
    omega
  have hq := straightPositiveHalfPath_supportedInLinkPositiveHalf
    τ 0 z hz length
  exact eventuallyLinkCrossingFamilyNormSquare_reflectedFullPath_of_support
    rho Psi τ z hz (straightPositiveHalfPath τ z length)
    hPsiCov hPsi hq

/-- Every pair of explicit transverse straight half-arms supplies the mixed
Gram-family Cauchy--Schwarz certificate whose diagonal terms are the two
corresponding reflected full lines.  Taking lengths `a` and `a + 2` is the
geometric input for adjacent log-convexity; the mixed observable is kept
explicit until its translation to the centered `a + 1` line is identified. -/
theorem transverseStraightArms_eventuallyLinkCrossingFamilyCauchySchwarz
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (a b : ℕ) :
    EventuallyLinkCrossingFamilyCauchySchwarz (ι := Fin n)
      (Geometry.armAxis hd)
      (let τ := Geometry.armAxis hd
       let ya := Path.advance (step z (.forward τ)) (.forward τ) a
       let yb := Path.advance (step z (.forward τ)) (.forward τ) b
       let Psi := transverseAxialEndpoint hd eta ya T
       let Xi := transverseAxialEndpoint hd eta yb T
       reflectedMixedObservable rho Psi Xi τ 0 z hz
         (straightPositiveHalfPath τ z a)
         (straightPositiveHalfPath τ z b))
      (let τ := Geometry.armAxis hd
       let ya := Path.advance (step z (.forward τ)) (.forward τ) a
       let Psi := transverseAxialEndpoint hd eta ya T
       screenedObservable rho (Psi.linkPullback τ 0) Psi
         (reflectedFullPath τ 0 z hz
           (straightPositiveHalfPath τ z a)))
      (let τ := Geometry.armAxis hd
       let yb := Path.advance (step z (.forward τ)) (.forward τ) b
       let Xi := transverseAxialEndpoint hd eta yb T
       screenedObservable rho (Xi.linkPullback τ 0) Xi
         (reflectedFullPath τ 0 z hz
           (straightPositiveHalfPath τ z b))) := by
  let τ := Geometry.armAxis hd
  let ya := Path.advance (step z (.forward τ)) (.forward τ) a
  let yb := Path.advance (step z (.forward τ)) (.forward τ) b
  let Psi := transverseAxialEndpoint hd eta ya T
  let Xi := transverseAxialEndpoint hd eta yb T
  have hcoordA : ya τ = 0 + 1 + a := by
    exact straightPositiveHalfPath_target_coord τ 0 z hz a
  have hcoordB : yb τ = 0 + 1 + b := by
    exact straightPositiveHalfPath_target_coord τ 0 z hz b
  have hPsiCov : GaugeCovariantAt rho ya Psi :=
    transverseAxialEndpoint_covariant hd rho eta ya T hT
  have hXiCov : GaugeCovariantAt rho yb Xi :=
    transverseAxialEndpoint_covariant hd rho eta yb T hT
  have hPsiAt : Psi.SupportedInLinkPositiveHalf τ (ya τ - 1) :=
    transverseAxialEndpoint_supportedInLinkPositiveHalf hd eta ya T
  have hXiAt : Xi.SupportedInLinkPositiveHalf τ (yb τ - 1) :=
    transverseAxialEndpoint_supportedInLinkPositiveHalf hd eta yb T
  have hPsi : Psi.SupportedInLinkPositiveHalf τ 0 := by
    apply hPsiAt.mono
    rw [hcoordA]
    omega
  have hXi : Xi.SupportedInLinkPositiveHalf τ 0 := by
    apply hXiAt.mono
    rw [hcoordB]
    omega
  have hqa := straightPositiveHalfPath_supportedInLinkPositiveHalf
    τ 0 z hz a
  have hqb := straightPositiveHalfPath_supportedInLinkPositiveHalf
    τ 0 z hz b
  exact eventuallyLinkCrossingFamilyCauchySchwarz_reflectedMixed_of_support
    rho Psi Xi τ z hz
    (straightPositiveHalfPath τ z a)
    (straightPositiveHalfPath τ z b)
    hPsiCov hXiCov hPsi hXi hqa hqb

/-- Concise named form of the explicit straight-arm norm-square
certificate. -/
theorem transverseStraightArmObservable_eventuallyFamilyNormSquare
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) :
    EventuallyLinkCrossingFamilyNormSquare (ι := Fin n)
      (Geometry.armAxis hd)
      (transverseStraightArmObservable hd rho eta T z hz length) := by
  simpa [transverseStraightArmObservable, transverseStraightArmEndpoint] using
    (transverseStraightArm_eventuallyLinkCrossingFamilyNormSquare
      hd rho eta T hT z hz length)

/-- Concise named form of the mixed certificate for two explicit arm
lengths. -/
theorem transverseStraightArmsMixedObservable_eventuallyFamilyCauchySchwarz
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (a b : ℕ) :
    EventuallyLinkCrossingFamilyCauchySchwarz (ι := Fin n)
      (Geometry.armAxis hd)
      (transverseStraightArmsMixedObservable hd rho eta T z hz a b)
      (transverseStraightArmObservable hd rho eta T z hz a)
      (transverseStraightArmObservable hd rho eta T z hz b) := by
  simpa [transverseStraightArmsMixedObservable,
    transverseStraightArmObservable, transverseStraightArmEndpoint] using
    (transverseStraightArms_eventuallyLinkCrossingFamilyCauchySchwarz
      hd rho eta T hT z hz a b)

/-- Infinite-volume Cauchy--Schwarz for two explicit straight gluelump
half-arms.  The representation coordinate has not been prematurely
contracted, so this form can feed the adjacent-translation and later corner
gluing steps. -/
theorem centeredInfiniteVolume_transverseStraightArmsMixed_cauchySchwarz
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (etaRep : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (etaRep.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (etaRep.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (exterior : ℕ → Configuration d G) (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (a b : ℕ) :
    Complex.normSq (∫ A,
        transverseStraightArmsMixedObservable hd rho etaRep T z hz a b A
        ∂centeredInfiniteVolumeMeasure exterior rho.wilsonPotential beta hbeta) ≤
      Complex.re (∫ A,
        transverseStraightArmObservable hd rho etaRep T z hz a A
        ∂centeredInfiniteVolumeMeasure exterior rho.wilsonPotential beta hbeta) *
      Complex.re (∫ A,
        transverseStraightArmObservable hd rho etaRep T z hz b A
        ∂centeredInfiniteVolumeMeasure exterior rho.wilsonPotential beta hbeta) := by
  exact centeredInfiniteVolume_linkCrossingFamilyCauchySchwarz_half
    exterior rho beta hbeta0 hbeta (Geometry.armAxis hd)
    (transverseStraightArmsMixedObservable hd rho etaRep T z hz a b)
    (transverseStraightArmObservable hd rho etaRep T z hz a)
    (transverseStraightArmObservable hd rho etaRep T z hz b)
    (transverseStraightArmsMixedObservable_eventuallyFamilyCauchySchwarz
      hd rho etaRep T hT z hz a b)

end

end YangMills.Gluelump.Propagation
