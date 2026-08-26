/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.CenterNeutral

/-!
# Representations whose kernel is the center

This file isolates the purely algebraic conclusion needed from the Lie-group
theorem `ker Ad = Z(G)`.  The pinned Mathlib supplies `GroupLieAlgebra`, but it
does not yet define the group adjoint representation or its kernel theorem, so
the genuinely differential-geometric construction must not be disguised as an
algebraic axiom here.

`KernelIsCenter` is useful independently: it records the exact property that
the future complexified adjoint representation must satisfy, and immediately
implies center-neutrality.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The representation acts trivially precisely on the center of the group.
This pointwise formulation avoids committing to a particular bundled kernel
API for the future Lie-group adjoint representation. -/
def KernelIsCenter (rho : Representation k G V) : Prop :=
  ∀ g : G, rho g = LinearMap.id ↔ g ∈ Subgroup.center G

/-- A representation whose kernel is the center is center-neutral. -/
theorem KernelIsCenter.centerNeutral {rho : Representation k G V}
    (hrho : KernelIsCenter rho) : CenterNeutral rho := by
  intro z hz
  exact (hrho z).mpr hz

/-- For a representation with central kernel, center-neutrality of another
representation says exactly that the first kernel is contained in the second
kernel.  This is the algebraic factor-through-the-quotient criterion used in
the sufficiency argument. -/
theorem centerNeutral_iff_kernel_le_of_kernelIsCenter
    {rho sigma : Representation k G V} (hrho : KernelIsCenter rho) :
    CenterNeutral sigma ↔
      ∀ g : G, rho g = LinearMap.id → sigma g = LinearMap.id := by
  constructor
  · intro hsigma g hg
    exact hsigma g ((hrho g).mp hg)
  · intro h z hz
    exact h z ((hrho z).mpr hz)

/-- A center-neutral representation descends canonically to the quotient by
the center. -/
noncomputable def centerQuotient (rho : Representation k G V)
    (hrho : CenterNeutral rho) :
    Representation k (G ⧸ Subgroup.center G) V := by
  letI : (Subgroup.center G).Normal := inferInstance
  letI : IsTrivial (rho.comp (Subgroup.center G).subtype) :=
    ⟨fun z ↦ hrho z.1 z.2⟩
  exact rho.ofQuotient (Subgroup.center G)

/-- Pulling the descended representation back along the quotient map recovers
the original action pointwise. -/
@[simp]
theorem centerQuotient_coe_apply (rho : Representation k G V)
    (hrho : CenterNeutral rho) (g : G) (v : V) :
    centerQuotient rho hrho (g : G ⧸ Subgroup.center G) v = rho g v := by
  letI : (Subgroup.center G).Normal := inferInstance
  letI : IsTrivial (rho.comp (Subgroup.center G).subtype) :=
    ⟨fun z ↦ hrho z.1 z.2⟩
  exact Representation.ofQuotient_coe_apply rho (Subgroup.center G) g v

end YangMills.Gluelump.RepresentationTheory
