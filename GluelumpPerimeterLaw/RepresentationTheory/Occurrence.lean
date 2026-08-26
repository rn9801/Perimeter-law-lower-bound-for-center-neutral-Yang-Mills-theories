/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.RepresentationTheory.Irreducible

/-!
# Occurrence through nonzero intertwiners

This file fixes the Lean-facing occurrence convention for the gluelump
development. An irreducible representation occurs in another representation
when there is a nonzero intertwining map into it. Mathlib's irreducible-map
dichotomy then identifies this with an injective equivariant realization.

This resolves roadmap item RT-02 at the algebraic representation level. It is
deliberately independent of the lattice-gauge and Douglas compatibility layers.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- An algebraic representation `tau` occurs in `rho` when there is a nonzero
equivariant linear map from the representation space of `tau` to that of
`rho`. -/
def OccursIn (tau : Representation k G V) (rho : Representation k G W) : Prop :=
  ∃ f : IntertwiningMap tau rho, f ≠ 0

/-- A nonzero intertwiner from an irreducible representation is injective. -/
theorem injective_of_irreducible_of_ne_zero
    {tau : Representation k G V} {rho : Representation k G W}
    [tau.IsIrreducible] (f : IntertwiningMap tau rho) (hf : f ≠ 0) :
    Function.Injective f :=
  (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

/-- The nonzero-intertwiner occurrence convention is equivalent to existence
of an injective equivariant map when the source is irreducible. -/
theorem occursIn_iff_exists_injective
    {tau : Representation k G V} {rho : Representation k G W}
    [tau.IsIrreducible] [Nontrivial V] :
    OccursIn tau rho ↔ ∃ f : IntertwiningMap tau rho, Function.Injective f := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, injective_of_irreducible_of_ne_zero f hf⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro hzero
    obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    apply hvw
    apply hf
    simp [hzero]

/-- An explicit injective intertwiner witnesses occurrence of an irreducible
representation. -/
theorem occursIn_of_injective
    {tau : Representation k G V} {rho : Representation k G W}
    [tau.IsIrreducible] [Nontrivial V] (f : IntertwiningMap tau rho)
    (hf : Function.Injective f) : OccursIn tau rho :=
  occursIn_iff_exists_injective.mpr ⟨f, hf⟩

/-- Occurrence is preserved by postcomposition with an injective intertwiner. -/
theorem OccursIn.postcomp
    {tau : Representation k G V} {rho : Representation k G W}
    {U : Type*} [AddCommGroup U] [Module k U]
    {pi : Representation k G U}
    (h : OccursIn tau rho) (e : IntertwiningMap rho pi)
    (he : Function.Injective e) : OccursIn tau pi := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.comp f, ?_⟩
  intro hzero
  apply hf
  apply IntertwiningMap.ext
  ext v
  apply he
  have hv := congrArg (fun q : IntertwiningMap tau pi => q v) hzero
  simpa using hv

end YangMills.Gluelump.RepresentationTheory
