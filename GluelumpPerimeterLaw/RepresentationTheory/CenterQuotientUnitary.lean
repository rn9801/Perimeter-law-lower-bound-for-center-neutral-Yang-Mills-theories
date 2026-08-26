/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.HilbertConjugationSpan
import GluelumpPerimeterLaw.RepresentationTheory.Quotient

/-!
# Continuous unitary representations on the quotient by the center

This file upgrades the algebraic quotient construction to the fixed unitary
matrix interface required by the Haar tensor-generation theorem.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation YangMills.Wilson
open scoped Matrix

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {n : ℕ}

/-- A center-neutral continuous unitary matrix representation descends to a
continuous unitary matrix representation of the quotient by the center. -/
def centerQuotientUnitaryRepData
    (rho : ContinuousUnitaryRepData G n)
    (hcenter : CenterNeutral (asRepresentation rho)) :
    ContinuousUnitaryRepData (G ⧸ Subgroup.center G) n where
  ρ := QuotientGroup.lift (Subgroup.center G) rho.ρ (by
    intro z hz
    apply Subtype.ext
    exact (centerNeutral_asRepresentation_iff rho).mp hcenter z hz)
  continuous_ρ := by
    apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
    simpa only [Function.comp_apply, QuotientGroup.lift_mk] using rho.continuous_ρ
  dimension_pos := rho.dimension_pos

@[simp]
theorem centerQuotientUnitaryRepData_coe
    (rho : ContinuousUnitaryRepData G n)
    (hcenter : CenterNeutral (asRepresentation rho)) (g : G) :
    (centerQuotientUnitaryRepData rho hcenter).ρ
      (g : G ⧸ Subgroup.center G) = rho.ρ g :=
  rfl

/-- Equivariantly equivalent representations have the same identity
operators, pointwise. -/
theorem representationEquiv_map_eq_id_iff
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {eta : Representation ℂ G W}
    (e : rho.Equiv eta) (g : G) :
    rho g = LinearMap.id ↔ eta g = LinearMap.id := by
  constructor
  · intro h
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    calc
      eta g (e v) = e (rho g v) :=
        (IntertwiningMap.isIntertwining rho eta e.toIntertwiningMap g v).symm
      _ = e v := by rw [h]; rfl
      _ = LinearMap.id (e v) := rfl
  · intro h
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    calc
      e (rho g v) = eta g (e v) :=
        IntertwiningMap.isIntertwining rho eta e.toIntertwiningMap g v
      _ = e v := by rw [h]; rfl
      _ = e (LinearMap.id v) := rfl

/-- The contravariant equivalence induced on algebraic duals. -/
def representationEquiv_dualContravariant
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {eta : Representation ℂ G W}
    (e : rho.Equiv eta) : eta.dual.Equiv rho.dual where
  toLinearEquiv := e.toLinearEquiv.dualMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    ext v
    change f (eta g⁻¹ (e v)) = f (e (rho g⁻¹ v))
    exact congrArg f
      (IntertwiningMap.isIntertwining rho eta e.toIntertwiningMap (g⁻¹) v).symm

/-- The property `kernel = center` is invariant under equivariant linear
equivalence. -/
theorem KernelIsCenter.equiv_iff
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {eta : Representation ℂ G W}
    (e : rho.Equiv eta) : KernelIsCenter rho ↔ KernelIsCenter eta := by
  constructor
  · intro h g
    rw [← representationEquiv_map_eq_id_iff e g]
    exact h g
  · intro h g
    rw [representationEquiv_map_eq_id_iff e g]
    exact h g

/-- Center neutrality is invariant under equivariant equivalence. -/
theorem representationEquiv_centerNeutral_iff
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {eta : Representation ℂ G W}
    (e : rho.Equiv eta) : CenterNeutral rho ↔ CenterNeutral eta := by
  constructor
  · intro h z hz
    exact (representationEquiv_map_eq_id_iff e z).mp (h z hz)
  · intro h z hz
    exact (representationEquiv_map_eq_id_iff e z).mpr (h z hz)

/-- Self-duality descends through the quotient by the center. -/
def centerQuotientSelfDual
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (hcenter : CenterNeutral rho)
    (self : rho.Equiv rho.dual) :
    (centerQuotient rho hcenter).Equiv
      (centerQuotient rho hcenter).dual where
  toLinearEquiv := self.toLinearEquiv
  isIntertwining' q := by
    induction q using QuotientGroup.induction_on with
    | _ g =>
      apply LinearMap.ext
      intro v
      ext w
      change self (centerQuotient rho hcenter
          (g : G ⧸ Subgroup.center G) v) w =
        self v (centerQuotient rho hcenter
          ((g : G ⧸ Subgroup.center G)⁻¹) w)
      rw [centerQuotient_coe_apply]
      rw [← QuotientGroup.mk_inv, centerQuotient_coe_apply]
      exact congrArg (fun f : Module.Dual ℂ V => f w)
        (IntertwiningMap.isIntertwining rho rho.dual
          self.toIntertwiningMap g v)

/-- The algebraic representation underlying unitary descent is pointwise the
canonical algebraic quotient representation. -/
def centerQuotientUnitaryRepEquiv
    (rho : ContinuousUnitaryRepData G n)
    (hcenter : CenterNeutral (asRepresentation rho)) :
    (asRepresentation (centerQuotientUnitaryRepData rho hcenter)).Equiv
      (centerQuotient (asRepresentation rho) hcenter) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' q := by
    induction q using QuotientGroup.induction_on with
    | _ g =>
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.refl_apply, centerQuotient_coe_apply,
        asRepresentation_apply, centerQuotientUnitaryRepData_coe]

/-- Fixed coordinates for the conjugation span still have kernel exactly the
center. -/
theorem hilbertConjSpanCoordinate_kernelIsCenter
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) :
    KernelIsCenter (asRepresentation
      (hilbertConjSpanUnitaryRepData sigma)) :=
  (KernelIsCenter.equiv_iff
    (hilbertConjSpanCoordinateEquiv sigma)).mpr
      (conjSpanRep_kernelIsCenter sigma hsigma)

/-- The fixed-coordinate conjugation-span representation is self-dual. -/
def hilbertConjSpanCoordinateSelfDual
    (sigma : ContinuousUnitaryRepData G n) :
    (asRepresentation (hilbertConjSpanUnitaryRepData sigma)).Equiv
      (asRepresentation (hilbertConjSpanUnitaryRepData sigma)).dual :=
  let e := hilbertConjSpanCoordinateEquiv sigma
  e.trans ((conjSpanSelfDual sigma).trans
    (representationEquiv_dualContravariant e))

/-- The fixed continuous unitary conjugation-span representation on
`G / Z(G)`. -/
def conjSpanCenterQuotientUnitaryRepData
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) :
    ContinuousUnitaryRepData (G ⧸ Subgroup.center G)
      (Module.finrank ℂ (HilbertConjSpan sigma)) :=
  let rho := hilbertConjSpanUnitaryRepData sigma
  centerQuotientUnitaryRepData rho
    (hilbertConjSpanCoordinate_kernelIsCenter sigma hsigma).centerNeutral

/-- Quotienting the exact central kernel makes the conjugation-span matrix
representation faithful. -/
theorem conjSpanCenterQuotientUnitaryRepData_injective
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) :
    Function.Injective (conjSpanCenterQuotientUnitaryRepData sigma hsigma).ρ := by
  let rho := hilbertConjSpanUnitaryRepData sigma
  let hk : KernelIsCenter (asRepresentation rho) :=
    hilbertConjSpanCoordinate_kernelIsCenter sigma hsigma
  let data := centerQuotientUnitaryRepData rho hk.centerNeutral
  let e := centerQuotientUnitaryRepEquiv rho hk.centerNeutral
  intro q₁ q₂ hq
  apply centerQuotient_injective_of_kernelIsCenter (asRepresentation rho) hk
  apply LinearMap.ext
  intro v
  have he₁ := IntertwiningMap.isIntertwining
    (asRepresentation data) (centerQuotient (asRepresentation rho) hk.centerNeutral)
    e.toIntertwiningMap q₁ v
  have he₂ := IntertwiningMap.isIntertwining
    (asRepresentation data) (centerQuotient (asRepresentation rho) hk.centerNeutral)
    e.toIntertwiningMap q₂ v
  have hdata : asRepresentation data q₁ v = asRepresentation data q₂ v := by
    have hq' : data.ρ q₁ = data.ρ q₂ := hq
    change (data.ρ q₁ : Matrix
        (Fin (Module.finrank ℂ (HilbertConjSpan sigma)))
        (Fin (Module.finrank ℂ (HilbertConjSpan sigma))) ℂ) *ᵥ v =
      (data.ρ q₂ : Matrix
        (Fin (Module.finrank ℂ (HilbertConjSpan sigma)))
        (Fin (Module.finrank ℂ (HilbertConjSpan sigma))) ℂ) *ᵥ v
    rw [hq']
  exact he₁.symm.trans (hdata.trans he₂)

/-- The faithful quotient conjugation-span representation remains
self-dual. -/
def conjSpanCenterQuotientSelfDual
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ) :
    (asRepresentation
      (conjSpanCenterQuotientUnitaryRepData sigma hsigma)).Equiv
      (asRepresentation
        (conjSpanCenterQuotientUnitaryRepData sigma hsigma)).dual :=
  let rho := hilbertConjSpanUnitaryRepData sigma
  let hk : KernelIsCenter (asRepresentation rho) :=
    hilbertConjSpanCoordinate_kernelIsCenter sigma hsigma
  let e := centerQuotientUnitaryRepEquiv rho hk.centerNeutral
  e.trans ((centerQuotientSelfDual (asRepresentation rho) hk.centerNeutral
    (hilbertConjSpanCoordinateSelfDual sigma)).trans
      (representationEquiv_dualContravariant e))

end

end YangMills.Gluelump.RepresentationTheory
