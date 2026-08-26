/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.TensorPower
import YangMills.Wilson.Representation

/-!
# Algebraic representation underlying fixed unitary matrices

This file is the narrow adapter between the project's Wilson-facing
`ContinuousUnitaryRepData` and Mathlib's algebraic `Representation` API.  It
does not change either core abstraction.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson
open scoped Matrix

noncomputable section

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G]

/-- Forget continuity and unitarity, retaining the algebraic matrix action on
column vectors. -/
def asRepresentation (rho : ContinuousUnitaryRepData G n) :
    Representation ℂ G (Fin n → ℂ) where
  toFun g := Matrix.toLin' (rho.ρ g : Matrix (Fin n) (Fin n) ℂ)
  map_one' := by
    ext v i
    simp
  map_mul' g h := by
    ext v i
    simp [Module.End.mul_apply]

@[simp]
theorem asRepresentation_apply (rho : ContinuousUnitaryRepData G n)
    (g : G) (v : Fin n → ℂ) :
    asRepresentation rho g v =
      (rho.ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ v :=
  rfl

/-- Matrix central-triviality is exactly center neutrality of the underlying
algebraic representation. -/
theorem centerNeutral_asRepresentation_iff
    (rho : ContinuousUnitaryRepData G n) :
    CenterNeutral (asRepresentation rho) ↔
      ∀ z : G, z ∈ Subgroup.center G →
        (rho.ρ z : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  constructor
  · intro h z hz
    have hzrep := h z hz
    exact Matrix.toLin'.injective (by simpa [asRepresentation] using hzrep)
  · intro h z hz
    change Matrix.toLin' (rho.ρ z : Matrix (Fin n) (Fin n) ℂ) = LinearMap.id
    rw [h z hz, Matrix.toLin'_one]

end

end YangMills.Gluelump.RepresentationTheory
