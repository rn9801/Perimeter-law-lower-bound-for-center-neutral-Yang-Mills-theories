/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Observable
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Vector-valued local endpoint fields

Gluelump endpoints are finite-dimensional vector- or covector-valued
cylindrical functions. This module supplies the local-field analogue of the
project's scalar `LocalObservable`, with the same explicit finite edge-support
convention. Scalar components recover ordinary local observables, which is the
bridge required by the existing reflection-positivity APIs.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

/-- A continuous field with values in `E` and an explicit finite edge support.
The recorded support need not be minimal. -/
structure LocalField (d : ℕ) (G E : Type*) [TopologicalSpace G]
    [TopologicalSpace E] where
  toContinuousMap : C(Configuration d G, E)
  support : Finset (PositiveEdge d)
  dependsOn_support : DependsOn toContinuousMap (support : Set (PositiveEdge d))

namespace LocalField

variable {d : ℕ} {G E F : Type*} [TopologicalSpace G]
  [TopologicalSpace E] [TopologicalSpace F]

instance : CoeFun (LocalField d G E) fun _ => Configuration d G → E :=
  ⟨fun Phi => Phi.toContinuousMap⟩

@[simp]
theorem coe_apply (Phi : LocalField d G E) (A : Configuration d G) :
    Phi.toContinuousMap A = Phi A :=
  rfl

/-- Replace a local field's recorded support by a larger finite support. -/
def enlarge (Phi : LocalField d G E) (S : Finset (PositiveEdge d))
    (h : Phi.support ⊆ S) : LocalField d G E where
  toContinuousMap := Phi.toContinuousMap
  support := S
  dependsOn_support := by
    intro A B hAB
    exact Phi.dependsOn_support fun e he => hAB e (h he)

@[simp]
theorem enlarge_apply (Phi : LocalField d G E) (S : Finset (PositiveEdge d))
    (h : Phi.support ⊆ S) (A : Configuration d G) :
    Phi.enlarge S h A = Phi A :=
  by change Phi.toContinuousMap A = Phi.toContinuousMap A; rfl

/-- Postcompose a local field with a continuous map. Its edge support is
unchanged. -/
def postcomp (Phi : LocalField d G E) (f : C(E, F)) : LocalField d G F where
  toContinuousMap := f.comp Phi.toContinuousMap
  support := Phi.support
  dependsOn_support := fun _A _B h => congrArg f (Phi.dependsOn_support h)

@[simp]
theorem postcomp_apply (Phi : LocalField d G E) (f : C(E, F))
    (A : Configuration d G) :
    Phi.postcomp f A = f (Phi A) :=
  rfl

/-- Pull a local field back along lattice translation. -/
def translatePullback (v : Site d) (Phi : LocalField d G E) :
    LocalField d G E where
  toContinuousMap := Phi.toContinuousMap.comp
    ⟨Gauge.LocalObservable.translateConfiguration v,
      Gauge.LocalObservable.continuous_translateConfiguration v⟩
  support := Phi.support.image (PositiveEdge.translate v)
  dependsOn_support := by
    intro A B h
    apply Phi.dependsOn_support
    intro e he
    exact h (e.translate v) (Finset.mem_image.mpr ⟨e, he, rfl⟩)

@[simp]
theorem translatePullback_apply (v : Site d) (Phi : LocalField d G E)
    (A : Configuration d G) :
    Phi.translatePullback v A =
      Phi (Gauge.LocalObservable.translateConfiguration v A) :=
  rfl

section Components

variable {n : ℕ}

/-- A coordinate of a finite-dimensional endpoint field is an ordinary local
observable with the same support. -/
def component (Phi : LocalField d G (Fin n → ℂ)) (i : Fin n) :
    LocalObservable d G :=
  { toContinuousMap :=
      ⟨fun A => Phi A i, continuous_apply i |>.comp Phi.toContinuousMap.continuous⟩
    support := Phi.support
    dependsOn_support := fun _A _B h => congrFun (Phi.dependsOn_support h) i }

@[simp]
theorem component_apply (Phi : LocalField d G (Fin n → ℂ))
    (i : Fin n) (A : Configuration d G) :
    Phi.component i A = Phi A i :=
  rfl

end Components

section Bounds

variable {n : ℕ} [CompactSpace G]

/-- A local endpoint field on the compact configuration space, viewed as a
bounded continuous function. -/
def toBoundedContinuousMap (Phi : LocalField d G (Fin n → ℂ)) :
    BoundedContinuousFunction (Configuration d G) (Fin n → ℂ) :=
  BoundedContinuousFunction.mkOfCompact Phi.toContinuousMap

/-- The canonical sup norm controls every pointwise endpoint value. -/
theorem norm_apply_le (Phi : LocalField d G (Fin n → ℂ))
    (A : Configuration d G) :
    ‖Phi A‖ ≤ ‖Phi.toBoundedContinuousMap‖ :=
  BoundedContinuousFunction.norm_coe_le_norm Phi.toBoundedContinuousMap A

end Bounds

end LocalField

end

end YangMills.Gluelump.Endpoint
