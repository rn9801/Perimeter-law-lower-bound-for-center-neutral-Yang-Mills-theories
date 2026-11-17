/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.Occurrence
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Center-neutral representations

This file proves the algebraic necessity half of Seiler screening in a reusable
form: an irreducible representation occurring in any center-neutral
representation is itself center-neutral. Tensor products and duals preserve
center neutrality, so the result applies once adjoint tensor powers are wired
to this interface.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A representation is center-neutral when every central group element acts
as the identity. -/
def CenterNeutral (rho : Representation k G V) : Prop :=
  ∀ z : G, z ∈ Subgroup.center G → rho z = LinearMap.id

/-- The trivial representation is center-neutral. -/
theorem centerNeutral_trivial :
    CenterNeutral (Representation.trivial k G V) := by
  intro z hz
  rfl

/-- Tensor products of center-neutral representations are center-neutral. -/
theorem CenterNeutral.tprod
    {rho : Representation k G V} {sigma : Representation k G W}
    (hrho : CenterNeutral rho) (hsigma : CenterNeutral sigma) :
    CenterNeutral (Representation.tprod rho sigma) := by
  intro z hz
  rw [Representation.tprod_apply, hrho z hz, hsigma z hz]
  ext v w
  simp

/-- The algebraic dual of a center-neutral representation is center-neutral. -/
theorem CenterNeutral.dual {rho : Representation k G V}
    (hrho : CenterNeutral rho) : CenterNeutral rho.dual := by
  intro z hz
  have hzinv : z⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hz
  ext f v
  simp [Representation.dual, hrho z⁻¹ hzinv]

/-- On a reflexive representation space, center neutrality of the algebraic
dual implies center neutrality of the original representation. -/
theorem centerNeutral_of_dual {rho : Representation k G V}
    [Module.IsReflexive k V] (hrho : CenterNeutral rho.dual) :
    CenterNeutral rho := by
  intro z hz
  ext v
  apply (Module.bijective_dual_eval k V).injective
  ext f
  have hzinv : z⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hz
  have hdual := hrho z⁻¹ hzinv
  have hf := LinearMap.congr_fun hdual f
  simpa [Representation.dual, Module.Dual.eval_apply] using
    LinearMap.congr_fun hf v

/-- Center neutrality is invariant under algebraic duality on a reflexive
representation space. -/
theorem centerNeutral_dual_iff {rho : Representation k G V}
    [Module.IsReflexive k V] :
    CenterNeutral rho.dual ↔ CenterNeutral rho :=
  ⟨centerNeutral_of_dual, CenterNeutral.dual⟩

/-- An irreducible representation occurring inside a center-neutral
representation is center-neutral. This is the core of the necessity direction
`screening -> center neutrality`. -/
theorem centerNeutral_of_occursIn
    {tau : Representation k G V} {rho : Representation k G W}
    [tau.IsIrreducible] (htau : OccursIn tau rho)
    (hrho : CenterNeutral rho) : CenterNeutral tau := by
  obtain ⟨f, hf⟩ := htau
  have hinjective := injective_of_irreducible_of_ne_zero f hf
  intro z hz
  ext v
  apply hinjective
  rw [f.isIntertwining, hrho z hz]
  simp

/-- A nonzero equivariant quotient of a center-neutral representation is
center-neutral when the target is irreducible.  This is the orientation used
by a screening map `adjointTensorPower → tau.dual`: irreducibility makes the
nonzero map surjective, after which central triviality descends through it. -/
theorem centerNeutral_of_nonzero_intertwiner_to_irreducible
    {rho : Representation k G V} {tau : Representation k G W}
    [tau.IsIrreducible] (f : IntertwiningMap rho tau) (hf : f ≠ 0)
    (hrho : CenterNeutral rho) : CenterNeutral tau := by
  have hsurjective : Function.Surjective f := by
    have hrange : f.range ≠ ⊥ := by
      intro hbot
      apply hf
      apply IntertwiningMap.ext
      ext v
      have hmem : f v ∈ f.range := ⟨v, rfl⟩
      rw [hbot] at hmem
      change f v ∈ (⊥ : Submodule k W) at hmem
      exact hmem
    have htop : f.range = ⊤ :=
      (eq_bot_or_eq_top f.range).resolve_left hrange
    intro w
    have hw : w ∈ f.range := by
      rw [htop]
      change w ∈ (⊤ : Submodule k W)
      exact Submodule.mem_top
    exact (IntertwiningMap.mem_range rho tau f w).mp hw
  intro z hz
  ext w
  obtain ⟨v, rfl⟩ := hsurjective w
  rw [← f.isIntertwining, hrho z hz]
  rfl

end YangMills.Gluelump.RepresentationTheory
