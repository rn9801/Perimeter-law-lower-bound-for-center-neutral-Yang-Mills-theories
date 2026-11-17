/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.Occurrence
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Irreducibility of the finite-dimensional contragredient

An invariant subspace of the algebraic dual has an invariant annihilator in
the original representation.  Finite-dimensional double-annihilator
identities therefore transport the irreducible-subspace dichotomy to the
dual.  This removes the former caller-supplied dual-irreducibility principle.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

noncomputable section

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The common annihilator in `V` of a subrepresentation of the
contragredient is stable under the original action. -/
def dualCoannihilatorSubrepresentation (rho : Representation k G V)
    (W : Subrepresentation rho.dual) : Subrepresentation rho where
  toSubmodule := W.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro phi hphi
    have hmem : rho.dual g⁻¹ phi ∈ W :=
      W.apply_mem_toSubmodule g⁻¹ hphi
    have hz := hv (rho.dual g⁻¹ phi) hmem
    simpa [Representation.dual] using hz

@[simp]
theorem dualCoannihilatorSubrepresentation_toSubmodule
    (rho : Representation k G V) (W : Subrepresentation rho.dual) :
    (dualCoannihilatorSubrepresentation rho W).toSubmodule =
      W.toSubmodule.dualCoannihilator :=
  rfl

/-- The algebraic dual of a nontrivial finite-dimensional irreducible
representation is irreducible. -/
theorem isIrreducible_dual (rho : Representation k G V)
    [Nontrivial V] [FiniteDimensional k V] [rho.IsIrreducible] :
    rho.dual.IsIrreducible := by
  letI : Nontrivial (Module.Dual k V) := inferInstance
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h =>
             bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
           eq_bot_or_eq_top := ?_ }
  intro W
  let P := dualCoannihilatorSubrepresentation rho W
  rcases eq_bot_or_eq_top P with hP | hP
  · right
    apply Subrepresentation.toSubmodule_injective
    have hco : W.toSubmodule.dualCoannihilator = ⊥ := by
      simpa [P] using congrArg Subrepresentation.toSubmodule hP
    calc
      W.toSubmodule =
          W.toSubmodule.dualCoannihilator.dualAnnihilator :=
        (Subspace.dualCoannihilator_dualAnnihilator_eq
          (W := W.toSubmodule)).symm
      _ = ⊤ := by rw [hco, Submodule.dualAnnihilator_bot]
      _ = (⊤ : Subrepresentation rho.dual).toSubmodule := rfl
  · left
    apply Subrepresentation.toSubmodule_injective
    have hco : W.toSubmodule.dualCoannihilator = ⊤ := by
      simpa [P] using congrArg Subrepresentation.toSubmodule hP
    calc
      W.toSubmodule =
          W.toSubmodule.dualCoannihilator.dualAnnihilator :=
        (Subspace.dualCoannihilator_dualAnnihilator_eq
          (W := W.toSubmodule)).symm
      _ = ⊥ := by rw [hco, Submodule.dualAnnihilator_top]
      _ = (⊥ : Subrepresentation rho.dual).toSubmodule := rfl

end

end YangMills.Gluelump.RepresentationTheory
