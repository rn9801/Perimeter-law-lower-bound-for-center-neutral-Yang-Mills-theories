/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.Center
import GluelumpPerimeterLaw.RepresentationTheory.TensorPower
import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix
import Mathlib.RepresentationTheory.Invariants

/-!
# Screening by tensor powers of a source representation

This file fixes the algebraic predicates used by Milestone A without yet
pretending that the pinned library has a complexified group adjoint
representation.  The suffix `By` is intentional: downstream code can use
these results for the adjoint representation once that representation has
been constructed, while the unqualified roadmap names remain reserved for
the genuine compact Lie-group specialization.

There is an important orientation issue.  A singlet in `tau ⊗ W` canonically
gives an intertwiner `tau.dual → W`.  The roadmap needs an intertwiner in the
opposite direction, `W → tau.dual`; passing between those two maps uses
complete reducibility (or invariant Hermitian orthogonal complements), not
only the tensor--Hom equivalence.  Accordingly no false purely algebraic
equivalence is stated below.
-/

namespace YangMills.Gluelump.RepresentationTheory

open Representation

universe u

variable {G V A : Type u} [Group G]
  [AddCommGroup V] [Module ℂ V]
  [AddCommGroup A] [Module ℂ A]

/-- A representation has a nonzero invariant vector. -/
def HasNonzeroInvariant (rho : Representation ℂ G V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ v ∈ rho.invariants

/-- The canonical evaluation map is an equivalence of a reflexive
representation with its double dual, including the group action. -/
noncomputable def evalRepresentationEquiv
    (tau : Representation ℂ G V) [Module.IsReflexive ℂ V] :
    tau.Equiv tau.dual.dual where
  toLinearEquiv := Module.evalEquiv ℂ V
  isIntertwining' g := by
    ext v f
    change f (tau g v) = (f ∘ₗ tau (g⁻¹)⁻¹) v
    simp

/-- A representation equivalence restricts to an equivalence of invariant
subspaces. -/
noncomputable def invariantsEquivOfEquiv
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    (e : rho.Equiv sigma) : rho.invariants ≃ₗ[ℂ] sigma.invariants where
  toFun v := ⟨e v.1, by
    intro g
    calc
      sigma g (e v.1) = e (rho g v.1) :=
        (IntertwiningMap.isIntertwining rho sigma
          e.toIntertwiningMap g v.1).symm
      _ = e v.1 := congrArg e (v.2 g)⟩
  invFun w := ⟨e.symm w.1, by
    intro g
    calc
      rho g (e.symm w.1) = e.symm (sigma g w.1) :=
        (IntertwiningMap.isIntertwining sigma rho
          e.symm.toIntertwiningMap g w.1).symm
      _ = e.symm w.1 := congrArg e.symm (w.2 g)⟩
  left_inv v := by
    apply Subtype.ext
    exact e.symm_apply_apply v.1
  right_inv w := by
    apply Subtype.ext
    exact e.apply_symm_apply w.1
  map_add' v w := by
    apply Subtype.ext
    exact map_add e v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul e c v.1

/-- The canonical tensor--Hom equivalence in the orientation actually
provided by linear algebra:

`(tau ⊗ W)^G ≃ Hom_G(tau.dual, W)`.

Reflexivity identifies `tau` with its double dual before applying Mathlib's
`dualTensorHom` equivalence. -/
noncomputable def singletIntertwinerEquiv
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (tau : Representation ℂ G V) (sigma : Representation ℂ G W) :
    (tau.tprod sigma).invariants ≃ₗ[ℂ] IntertwiningMap tau.dual sigma := by
  let etensor : (tau.tprod sigma).Equiv (tau.dual.dual.tprod sigma) :=
    { toLinearEquiv := TensorProduct.congr
        (Module.evalEquiv ℂ V) (LinearEquiv.refl ℂ W)
      isIntertwining' := by
        intro g
        ext v w
        change (Module.Dual.eval ℂ V (tau g v)) ⊗ₜ[ℂ] (sigma g w) =
          ((tau.dual.dual g) (Module.Dual.eval ℂ V v)) ⊗ₜ[ℂ]
            (sigma g w)
        congr 1
        ext f
        change f (tau g v) = (f ∘ₗ tau (g⁻¹)⁻¹) v
        simp }
  exact (invariantsEquivOfEquiv etensor).trans
    ((invariantsEquivOfEquiv
      (Representation.Equiv.dualTensorHom tau.dual sigma)).trans
        (Representation.invariantsEquivIntertwiningMap tau.dual sigma))

/-- A nonzero singlet is canonically equivalent to occurrence of the dual
representation in the other tensor factor.  Notice that the resulting map is
`tau.dual → W`, not the projection `W → tau.dual` needed by the endpoint;
the latter uses compact complete reducibility. -/
theorem hasNonzeroInvariant_tprod_iff_occursIn_dual
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (tau : Representation ℂ G V) (sigma : Representation ℂ G W) :
    HasNonzeroInvariant (tau.tprod sigma) ↔ OccursIn tau.dual sigma := by
  let e := singletIntertwinerEquiv tau sigma
  constructor
  · rintro ⟨v, hv, hinv⟩
    let v' : (tau.tprod sigma).invariants := ⟨v, hinv⟩
    refine ⟨e v', ?_⟩
    intro hezero
    apply hv
    have hvzero : v' = 0 := e.injective (by simpa using hezero)
    exact congrArg Subtype.val hvzero
  · rintro ⟨f, hf⟩
    let v := e.symm f
    refine ⟨v.1, ?_, v.2⟩
    intro hvzero
    apply hf
    have vvzero : v = 0 := Subtype.ext hvzero
    have := congrArg e vvzero
    simpa [v] using this

/-- Seiler's singlet condition relative to a specified screening source.
For the final theorem `adj` will be the complexified adjoint representation. -/
def SeilerScreenedBy (adj : Representation ℂ G A)
    (tau : Representation ℂ G V) : Prop :=
  ∃ m : ℕ, HasNonzeroInvariant (tau.tprod (tensorPower adj m))

/-- Seiler's singlet condition is exactly occurrence of the dual in one
tensor power.  This is the part of the singlet/intertwiner bridge supplied by
tensor--Hom alone. -/
theorem seilerScreenedBy_iff_exists_occursIn_dual
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    (adj : Representation ℂ G A) (tau : Representation ℂ G V) :
    SeilerScreenedBy adj tau ↔
      ∃ m : ℕ, OccursIn tau.dual (tensorPower adj m) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m,
      (hasNonzeroInvariant_tprod_iff_occursIn_dual tau
        (tensorPower adj m)).mp hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m,
      (hasNonzeroInvariant_tprod_iff_occursIn_dual tau
        (tensorPower adj m)).mpr hm⟩

/-- The necessity half of Seiler screening, proved directly in the canonical
occurrence orientation.  No choice of an invariant complement is needed. -/
theorem SeilerScreenedBy.centerNeutral
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible]
    (hscreen : SeilerScreenedBy adj tau)
    (hadj : CenterNeutral adj) : CenterNeutral tau := by
  obtain ⟨m, hm⟩ :=
    (seilerScreenedBy_iff_exists_occursIn_dual adj tau).mp hscreen
  exact centerNeutral_of_dual
    (centerNeutral_of_occursIn hm (hadj.tensorPower m))

/-- Seiler screening is center-neutral whenever the screening source has
kernel equal to the center. -/
theorem SeilerScreenedBy.centerNeutral_of_kernelIsCenter
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible]
    (hscreen : SeilerScreenedBy adj tau)
    (hadj : KernelIsCenter adj) : CenterNeutral tau :=
  hscreen.centerNeutral hadj.centerNeutral

/-- The computational screening condition used by the endpoint construction:
a tensor power of the screening source maps nontrivially and equivariantly to
the algebraic dual of the Wilson representation. -/
def HasScreeningIntertwinerBy (adj : Representation ℂ G A)
    (tau : Representation ℂ G V) : Prop :=
  ∃ m : ℕ, ∃ T : IntertwiningMap (tensorPower adj m) tau.dual, T ≠ 0

/-- Complete reducibility supplies this orientation symmetry: occurrence of
`sigma` in `rho` can be represented either by an embedding `sigma → rho` or
by a nonzero equivariant projection `rho → sigma`.  Keeping it named makes
the non-canonical compact-group input in the roadmap explicit. -/
def IntertwinerOrientationSymmetric
    {W : Type u} [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) : Prop :=
  OccursIn sigma rho ↔ ∃ T : IntertwiningMap rho sigma, T ≠ 0

/-! ## Temporary explicit compact representation-theory assumptions

The repository forbids proof placeholders.  The following three propositions
are therefore passed as named hypotheses to the general compact Lie-group
headline theorem.  They isolate exactly the standard results that remain to
be supplied by future Mathlib-level infrastructure; none is installed
globally as either an assumption or an instance.
-/

/-- Finite-dimensional irreducibility is preserved by algebraic duality. -/
def DualIrreducibilityPrinciple (G : Type u) [Group G] : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G W), rho.IsIrreducible → rho.dual.IsIrreducible

/-- Compact complete reducibility, stated in the precise two-orientation form
needed to turn a singlet embedding into an endpoint projection. -/
def CompactIntertwinerSplittingPrinciple (G : Type u) [Group G] : Prop :=
  ∀ {W U : Type u} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ U]
    (rho : Representation ℂ G W) (sigma : Representation ℂ G U),
      IntertwinerOrientationSymmetric rho sigma

/-- Faithful self-dual tensor generation on the quotient by the center,
pulled back to `G`.  `KernelIsCenter rho` is the faithful-on-`G/Z(G)`
hypothesis, while `CenterNeutral lambda` says that the target descends to the
same quotient. -/
def FaithfulSelfDualTensorGenerationPrinciple
    (G : Type u) [Group G] : Prop :=
  ∀ {W U : Type u} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ U]
    (rho : Representation ℂ G W) (lambda : Representation ℂ G U),
      KernelIsCenter rho → rho.Equiv rho.dual → lambda.IsIrreducible →
        CenterNeutral lambda →
          ∃ m : ℕ, ∃ T : IntertwiningMap (tensorPower rho m) lambda, T ≠ 0

/-- If equivariant occurrences in every relevant tensor power split, the
Seiler singlet and downstream projection formulations are equivalent. -/
theorem seilerScreenedBy_iff_hasScreeningIntertwinerBy
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    (adj : Representation ℂ G A) (tau : Representation ℂ G V)
    (hsplit : ∀ m : ℕ,
      IntertwinerOrientationSymmetric (tensorPower adj m) tau.dual) :
    SeilerScreenedBy adj tau ↔ HasScreeningIntertwinerBy adj tau := by
  rw [seilerScreenedBy_iff_exists_occursIn_dual]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨T, hT⟩ := (hsplit m).mp hm
    exact ⟨m, T, hT⟩
  · rintro ⟨m, T, hT⟩
    exact ⟨m, (hsplit m).mpr ⟨T, hT⟩⟩

/-! ## General adjoint-source specialization -/

/-- The representation-theoretic data supplied by the complexified group
adjoint representation.  Its construction from Lie-group differentiation and
the connectedness proof of `ker Ad = Z(G)` are deliberately isolated here. -/
structure AdjointScreeningData (G A : Type u) [Group G]
    [AddCommGroup A] [Module ℂ A] where
  /-- The complexified group adjoint representation. -/
  adjoint : Representation ℂ G A
  /-- Connectedness identifies its kernel with the group center. -/
  kernelIsCenter : KernelIsCenter adjoint
  /-- Compactness supplies an invariant inner product, hence self-duality. -/
  selfDual : adjoint.Equiv adjoint.dual

/-- Seiler screening for a chosen complexified adjoint source. -/
def SeilerScreened (D : AdjointScreeningData G A)
    (tau : Representation ℂ G V) : Prop :=
  SeilerScreenedBy D.adjoint tau

/-- The downstream projection form of screening for a chosen complexified
adjoint source. -/
def HasScreeningIntertwiner (D : AdjointScreeningData G A)
    (tau : Representation ℂ G V) : Prop :=
  HasScreeningIntertwinerBy D.adjoint tau

/-- Center neutrality produces the nonzero screening projection consumed by
the endpoint construction, assuming the standard dual-irreducibility and
faithful self-dual tensor-generation principles. -/
theorem centerNeutral_exists_screeningIntertwiner
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    (D : AdjointScreeningData G A)
    (hdual : DualIrreducibilityPrinciple G)
    (hgenerate : FaithfulSelfDualTensorGenerationPrinciple G)
    (tau : Representation ℂ G V) (htau : tau.IsIrreducible)
    (hcenter : CenterNeutral tau) : HasScreeningIntertwiner D tau := by
  exact hgenerate D.adjoint tau.dual D.kernelIsCenter D.selfDual
    (hdual tau htau) hcenter.dual

/-- Under compact complete reducibility, the literal Seiler singlet condition
is equivalent to the projection form used by endpoint code. -/
theorem seilerScreened_iff_exists_intertwiner
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    (D : AdjointScreeningData G A)
    (hsplit : CompactIntertwinerSplittingPrinciple G)
    (tau : Representation ℂ G V) :
    SeilerScreened D tau ↔ HasScreeningIntertwiner D tau := by
  exact seilerScreenedBy_iff_hasScreeningIntertwinerBy D.adjoint tau
    (fun m ↦ hsplit (tensorPower D.adjoint m) tau.dual)

/-- The advertised general representation-theory equivalence, with the three
standard compact representation-theory inputs explicit in its signature. -/
theorem centerNeutral_iff_seilerScreened
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ A]
    (D : AdjointScreeningData G A)
    (hdual : DualIrreducibilityPrinciple G)
    (hsplit : CompactIntertwinerSplittingPrinciple G)
    (hgenerate : FaithfulSelfDualTensorGenerationPrinciple G)
    (tau : Representation ℂ G V) (htau : tau.IsIrreducible) :
    CenterNeutral tau ↔ SeilerScreened D tau := by
  letI : tau.dual.IsIrreducible := hdual tau htau
  constructor
  · intro hcenter
    apply (seilerScreened_iff_exists_intertwiner D hsplit tau).mpr
    exact centerNeutral_exists_screeningIntertwiner D hdual hgenerate
      tau htau hcenter
  · intro hscreen
    exact SeilerScreenedBy.centerNeutral hscreen D.kernelIsCenter.centerNeutral

/-- Unpack a screening-intertwiner witness. -/
theorem hasScreeningIntertwinerBy_iff
    (adj : Representation ℂ G A) (tau : Representation ℂ G V) :
    HasScreeningIntertwinerBy adj tau ↔
      ∃ m : ℕ, ∃ T : IntertwiningMap (tensorPower adj m) tau.dual, T ≠ 0 :=
  Iff.rfl

/-- Necessity in the exact orientation consumed downstream: if the screening
source is center-neutral and a tensor power maps nontrivially onto the
irreducible dual Wilson representation, then that dual is center-neutral. -/
theorem HasScreeningIntertwinerBy.centerNeutral_dual
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible]
    (hscreen : HasScreeningIntertwinerBy adj tau)
    (hadj : CenterNeutral adj) : CenterNeutral tau.dual := by
  obtain ⟨m, T, hT⟩ := hscreen
  exact centerNeutral_of_nonzero_intertwiner_to_irreducible T hT
    (hadj.tensorPower m)

/-- Screening implies center neutrality of the original Wilson
representation once finite-dimensional reflexivity is available. -/
theorem HasScreeningIntertwinerBy.centerNeutral
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible] [Module.IsReflexive ℂ V]
    (hscreen : HasScreeningIntertwinerBy adj tau)
    (hadj : CenterNeutral adj) : CenterNeutral tau :=
  centerNeutral_of_dual (hscreen.centerNeutral_dual hadj)

/-- The same necessity statement with the center-kernel property expected of
the complexified adjoint representation. -/
theorem HasScreeningIntertwinerBy.centerNeutral_dual_of_kernelIsCenter
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible]
    (hscreen : HasScreeningIntertwinerBy adj tau)
    (hadj : KernelIsCenter adj) : CenterNeutral tau.dual :=
  hscreen.centerNeutral_dual hadj.centerNeutral

/-- The center-neutrality necessity theorem in the hypotheses expected for a
finite-dimensional irreducible Wilson representation and an adjoint source. -/
theorem HasScreeningIntertwinerBy.centerNeutral_of_kernelIsCenter
    {adj : Representation ℂ G A} {tau : Representation ℂ G V}
    [tau.dual.IsIrreducible] [Module.IsReflexive ℂ V]
    (hscreen : HasScreeningIntertwinerBy adj tau)
    (hadj : KernelIsCenter adj) : CenterNeutral tau :=
  hscreen.centerNeutral hadj.centerNeutral

end YangMills.Gluelump.RepresentationTheory
