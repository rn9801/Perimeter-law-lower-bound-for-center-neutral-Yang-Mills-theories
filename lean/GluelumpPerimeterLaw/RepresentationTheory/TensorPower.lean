/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.CenterNeutral
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Iterated tensor powers of an algebraic representation

The gluelump screening condition uses ordinary tensor powers of the adjoint
representation. Mathlib supplies homogeneous `TensorPower` carriers and the
functorial `PiTensorProduct.map`; this file combines them into a representation.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation
open scoped TensorProduct

universe uK uG uV uW

variable {k : Type uK} {G : Type uG} {V : Type uV} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The diagonal family of operators induced by a representation on `m`
tensor factors. -/
def tensorPowerFamily (rho : Representation k G V) (m : ℕ) :
    G →* ((i : Fin m) → V →ₗ[k] V) where
  toFun g := fun _ => rho g
  map_one' := by ext i v; simp
  map_mul' g h := by ext i v; simp [Module.End.mul_apply]

/-- The ordinary homogeneous tensor-power representation. -/
noncomputable def tensorPower (rho : Representation k G V) (m : ℕ) :
    Representation k G (⨂[k]^m V) :=
  (PiTensorProduct.mapMonoidHom (R := k) (s := fun _ : Fin m => V)).comp
    (tensorPowerFamily rho m)

/-- Tensor powers of a finite-dimensional vector space are finite-dimensional. -/
noncomputable instance tensorPowerFiniteDimensional
    [FiniteDimensional k V] (m : ℕ) :
    FiniteDimensional k (⨂[k]^m V) :=
  (Basis.piTensorProduct
    (fun _ : Fin m ↦ Module.Basis.ofVectorSpace k V)).finiteDimensional_of_finite

@[simp]
theorem tensorPower_apply (rho : Representation k G V) (m : ℕ) (g : G) :
    tensorPower rho m g = PiTensorProduct.map (fun _ : Fin m => rho g) :=
  rfl

@[simp]
theorem tensorPower_tprod (rho : Representation k G V) (m : ℕ)
    (g : G) (v : Fin m → V) :
    tensorPower rho m g (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (fun i => rho g (v i)) := by
  simp [tensorPower, tensorPowerFamily]

/-- An equivariant equivalence induces an equivariant equivalence on every
homogeneous tensor power. -/
noncomputable def tensorPowerEquiv
    {W : Type uW} [AddCommGroup W] [Module k W]
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : rho.Equiv sigma) (m : ℕ) :
    (tensorPower rho m).Equiv (tensorPower sigma m) where
  toLinearEquiv := PiTensorProduct.congr (fun _ : Fin m => e.toLinearEquiv)
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change PiTensorProduct.congr (fun _ : Fin m => e.toLinearEquiv)
        (tensorPower rho m g (PiTensorProduct.tprod k v)) =
      tensorPower sigma m g
        (PiTensorProduct.congr (fun _ : Fin m => e.toLinearEquiv)
          (PiTensorProduct.tprod k v))
    rw [tensorPower_tprod, PiTensorProduct.congr_tprod,
      PiTensorProduct.congr_tprod, tensorPower_tprod]
    congr 1
    funext i
    exact IntertwiningMap.isIntertwining rho sigma
      e.toIntertwiningMap g (v i)

/-- Every tensor power of a center-neutral representation is center-neutral. -/
theorem CenterNeutral.tensorPower {rho : Representation k G V}
    (hrho : CenterNeutral rho) (m : ℕ) :
    CenterNeutral (tensorPower rho m) := by
  intro z hz
  rw [tensorPower_apply, hrho z hz]
  exact PiTensorProduct.map_id

/-- An irreducible representation occurring in a tensor power of a
center-neutral representation is center-neutral. Applied to the adjoint
representation, this is the algebraic necessity direction of Seiler
screening. -/
theorem centerNeutral_of_occursIn_tensorPower
    {W : Type uW} [AddCommGroup W] [Module k W]
    {tau : Representation k G W} {rho : Representation k G V}
    [tau.IsIrreducible] {m : ℕ}
    (hoccurs : OccursIn tau (tensorPower rho m))
    (hrho : CenterNeutral rho) : CenterNeutral tau :=
  centerNeutral_of_occursIn hoccurs (hrho.tensorPower m)

end YangMills.Gluelump.RepresentationTheory
