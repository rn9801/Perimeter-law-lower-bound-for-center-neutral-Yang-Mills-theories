/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.TransverseConstruction
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixedCore

/-!
# Neutral straight screened-arm geometry

This file contains the straight positive-half path and the associated local
screened observables.  It is independent of any thermodynamic-limit or
strong-coupling construction.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson
open Endpoint
open scoped Matrix

noncomputable section

variable {d m n N : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- A straight positive half-arm beginning immediately beyond the crossing
link. -/
def straightPositiveHalfPath (τ : Fin d) (z : Site d) (length : ℕ) :
    Lattice.Cubic.Path (step z (.forward τ))
      (Path.advance (step z (.forward τ)) (.forward τ) length) :=
  Path.straight (step z (.forward τ)) (.forward τ) length

/-- Every stored edge of the straight positive half-arm lies strictly beyond
the link plane through `z`. -/
theorem straightPositiveHalfPath_supportedInLinkPositiveHalf
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k) (length : ℕ) :
    Endpoint.Path.SupportedInLinkPositiveHalf τ k
      (straightPositiveHalfPath τ z length) := by
  intro e he
  induction length with
  | zero =>
      change e ∈ ∅ at he
      simp at he
  | succ length ih =>
      simp only [straightPositiveHalfPath, Path.straight,
        Path.edgeSupport_cons, Finset.mem_insert] at he
      rcases he with rfl | he
      · change k <
          (step (Path.advance (step z (.forward τ)) (.forward τ) length)
            (.forward τ)) τ
        rw [Path.advance_eq]
        simp [step, SignedDirection.forward, SignedDirection.delta,
          unitVector, hz]
        omega
      · exact ih he

/-- The endpoint site of a length-`length` positive half-arm has arm
coordinate `k + 1 + length`. -/
theorem straightPositiveHalfPath_target_coord
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k) (length : ℕ) :
    Path.advance (step z (.forward τ)) (.forward τ) length τ =
      k + 1 + length := by
  rw [Path.advance_eq]
  simp [step, SignedDirection.forward, SignedDirection.delta,
    unitVector, hz]

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The concrete normalized endpoint at the far end of a positive straight
half-arm. -/
def transverseStraightArmEndpoint
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (length : ℕ) : LocalField d G (Fin n → ℂ) :=
  let τ := Geometry.armAxis hd
  transverseAxialEndpoint hd eta
    (Path.advance (step z (.forward τ)) (.forward τ) length) T

/-- The centered reflected full screened line associated to a positive
straight half-arm. -/
def transverseStraightArmObservable
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) :
    LocalObservable d G :=
  let τ := Geometry.armAxis hd
  let Psi := transverseStraightArmEndpoint hd eta T z length
  screenedObservable rho (Psi.linkPullback τ 0) Psi
    (reflectedFullPath τ 0 z hz (straightPositiveHalfPath τ z length))

/-- The index-preserving mixed screened line between two explicit positive
straight half-arms. -/
def transverseStraightArmsMixedObservable
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (a b : ℕ) :
    LocalObservable d G :=
  let τ := Geometry.armAxis hd
  reflectedMixedObservable rho
    (transverseStraightArmEndpoint hd eta T z a)
    (transverseStraightArmEndpoint hd eta T z b)
    τ 0 z hz (straightPositiveHalfPath τ z a)
      (straightPositiveHalfPath τ z b)

end

end YangMills.Gluelump.Propagation
