/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.Center
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Representation helpers for the quotient by the center

This file supplies the algebraic and elementary topological quotient facts
needed by the conjugation-span route.  It has no Lie-group dependencies.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

noncomputable section

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The center of a Hausdorff topological group is closed. -/
theorem isClosed_center [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] : IsClosed (Subgroup.center G : Set G) := by
  have hset : (Subgroup.center G : Set G) =
      ⋂ h : G, {g : G | h * g = g * h} := by
    ext g
    constructor
    · intro hg
      rw [Set.mem_iInter]
      intro h
      exact Subgroup.mem_center_iff.mp hg h
    · intro hg
      apply Subgroup.mem_center_iff.mpr
      intro h
      exact Set.mem_iInter.mp hg h
  rw [hset]
  apply isClosed_iInter
  intro h
  exact isClosed_eq (continuous_const.mul continuous_id)
    (continuous_id.mul continuous_const)

/-- Irreducibility is preserved when a center-neutral representation is
factored through the quotient by the center. -/
theorem centerQuotient_isIrreducible
    (rho : Representation k G V) (hrho : CenterNeutral rho)
    [Nontrivial V] [rho.IsIrreducible] :
    (centerQuotient rho hrho).IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h =>
             bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
           eq_bot_or_eq_top := ?_ }
  intro W
  let P : Subrepresentation rho := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule := fun g v hv => by
      have hmem := W.apply_mem_toSubmodule
        (g : G ⧸ Subgroup.center G) hv
      simpa only [centerQuotient_coe_apply] using hmem }
  rcases eq_bot_or_eq_top P with hP | hP
  · left
    apply Subrepresentation.toSubmodule_injective
    simpa [P] using congrArg Subrepresentation.toSubmodule hP
  · right
    apply Subrepresentation.toSubmodule_injective
    simpa [P] using congrArg Subrepresentation.toSubmodule hP

/-- If a representation has kernel exactly `N`, its representation on the
quotient by `N` is faithful.  Here `N` is the center and quotient descent is
provided by center neutrality. -/
theorem centerQuotient_injective_of_kernelIsCenter
    (rho : Representation k G V) (hrho : KernelIsCenter rho) :
    Function.Injective (centerQuotient rho hrho.centerNeutral) := by
  intro q₁ q₂ hq
  induction q₁ using QuotientGroup.induction_on with
  | _ g =>
    induction q₂ using QuotientGroup.induction_on with
    | _ h =>
      have hgh : rho g = rho h := by
        apply LinearMap.ext
        intro v
        have happ := LinearMap.congr_fun hq v
        simpa only [centerQuotient_coe_apply] using happ
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply (hrho (g / h)).mp
      rw [div_eq_mul_inv, map_mul, hgh]
      rw [← map_mul, show h * h⁻¹ = 1 by group, map_one]
      rfl

end

end YangMills.Gluelump.RepresentationTheory
