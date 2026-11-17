/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Covariance
import GluelumpPerimeterLaw.RepresentationTheory.DualUnitary
import GluelumpPerimeterLaw.RepresentationTheory.Screening
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Continuous screening forms in finite dimension

This file contains the representation-independent analytic bridge used by
both endpoint constructions.  An algebraic tensor-power intertwiner becomes
a continuous multilinear map in finite dimension.  The operational API maps
directly to the Wilson representation; the older dual-coordinate bridge is
retained for comparison and compatibility.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Wilson YangMills.Gluelump.RepresentationTheory
open Representation
open scoped TensorProduct

noncomputable section

universe u v w

variable {G : Type u} {A : Type w} {m n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]

/-! ## Algebraic-to-continuous finite-dimensional bridge -/

/-- Bundle a linear map out of a finite-dimensional complex normed space as
a continuous linear map.  Naming this one-variable bridge keeps downstream
constructions from repeatedly elaborating the finite-dimensional continuity
argument for complicated subtype spaces. -/
noncomputable def continuousLinearOfFiniteDimensional
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : A →ₗ[ℂ] V) : A →L[ℂ] V :=
  ⟨f, f.continuous_of_finiteDimensional⟩

@[simp]
theorem continuousLinearOfFiniteDimensional_apply
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : A →ₗ[ℂ] V) (a : A) :
    continuousLinearOfFiniteDimensional f a = f a :=
  rfl

/-- Every multilinear map between finite-dimensional complex normed spaces
has a canonical continuous realization.  Mathlib has the one-variable
statement; this iterates it through multilinear currying. -/
noncomputable def continuousMultilinearOfFiniteDimensional
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ∀ r : ℕ,
      MultilinearMap ℂ (fun _ : Fin r ↦ A) V →ₗ[ℂ]
        ContinuousMultilinearMap ℂ (fun _ : Fin r ↦ A) V
  | 0 =>
      { toFun := fun F ↦
          { toMultilinearMap := F
            cont := by
              change Continuous (⇑F)
              have hconst : (⇑F : (Fin 0 → A) → V) = fun _ ↦ F 0 := by
                funext x
                exact congrArg F (Subsingleton.elim x 0)
              rw [hconst]
              exact continuous_const }
        map_add' := by
          intro F H
          apply ContinuousMultilinearMap.ext
          intro x
          rfl
        map_smul' := by
          intro c F
          apply ContinuousMultilinearMap.ext
          intro x
          rfl }
  | r + 1 =>
      { toFun := fun F ↦
          let f : A →ₗ[ℂ]
              ContinuousMultilinearMap ℂ (fun _ : Fin r ↦ A) V :=
            (continuousMultilinearOfFiniteDimensional r).comp
              F.curryLeft
          let fc : A →L[ℂ]
              ContinuousMultilinearMap ℂ (fun _ : Fin r ↦ A) V :=
            ⟨f, f.continuous_of_finiteDimensional⟩
          fc.uncurryLeft
        map_add' := by
          intro F H
          apply ContinuousMultilinearMap.ext
          intro x
          simp only [ContinuousLinearMap.uncurryLeft_apply]
          change continuousMultilinearOfFiniteDimensional r
              ((F + H).curryLeft (x 0)) (Fin.tail x) =
            continuousMultilinearOfFiniteDimensional r
                (F.curryLeft (x 0)) (Fin.tail x) +
              continuousMultilinearOfFiniteDimensional r
                (H.curryLeft (x 0)) (Fin.tail x)
          rw [show (F + H).curryLeft (x 0) =
              F.curryLeft (x 0) + H.curryLeft (x 0) by rfl, map_add]
          rfl
        map_smul' := by
          intro c F
          apply ContinuousMultilinearMap.ext
          intro x
          simp only [ContinuousLinearMap.uncurryLeft_apply]
          change continuousMultilinearOfFiniteDimensional r
              ((c • F).curryLeft (x 0)) (Fin.tail x) =
            c • continuousMultilinearOfFiniteDimensional r
              (F.curryLeft (x 0)) (Fin.tail x)
          rw [show (c • F).curryLeft (x 0) =
              c • F.curryLeft (x 0) by rfl, map_smul]
          rfl }

@[simp]
theorem continuousMultilinearOfFiniteDimensional_apply
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (r : ℕ) (F : MultilinearMap ℂ (fun _ : Fin r ↦ A) V)
    (v : Fin r → A) :
    continuousMultilinearOfFiniteDimensional r F v = F v := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [continuousMultilinearOfFiniteDimensional,
        ContinuousLinearMap.uncurryLeft_apply]
      change continuousMultilinearOfFiniteDimensional r
          (F.curryLeft (v 0)) (Fin.tail v) = F v
      rw [ih]
      simpa [MultilinearMap.curryLeft_apply] using
        congrArg F (Fin.cons_self_tail v)

/-! ## Fixed coordinates on the Wilson dual -/

/-- Coordinates of an algebraic covector in the dual standard basis. -/
noncomputable def dualCoordinates (n : ℕ) :
    Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun

@[simp]
theorem dualCoordinates_apply
    (f : Module.Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    dualCoordinates n f i = f (Pi.single i 1) := by
  simp [dualCoordinates]

/-- In standard coordinates, Mathlib's algebraic dual representation agrees
with the ordinary action of its explicit unitary contragredient model.  This
legacy comparison is not used by the primal endpoint observable API. -/
theorem dualCoordinates_dual_action
    (rho : ContinuousUnitaryRepData G n) (g : G)
    (f : Module.Dual ℂ (Fin n → ℂ)) :
    dualCoordinates n ((asRepresentation rho).dual g f) =
      representationAction (dualUnitaryRepData rho) g
        (dualCoordinates n f) := by
  simpa [dualCoordinates, standardDualCoordinates, representationAction,
    asRepresentation_apply] using standardDualCoordinates_action rho g f

/-! ## The screening multilinear form -/

/-- Evaluate an algebraic tensor-power screening intertwiner on pure tensors
and express the resulting Wilson covector in standard coordinates. -/
noncomputable def screeningMultilinearForm
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual) :
    MultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) :=
  (dualCoordinates n).toLinearMap.compMultilinearMap
    (T.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ))

@[simp]
theorem screeningMultilinearForm_apply
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (v : Fin m → A) :
    screeningMultilinearForm adj rho T v =
      dualCoordinates n (T (PiTensorProduct.tprod ℂ v)) :=
  rfl

/-- The algebraic screening form, regarded as a continuous multilinear map.
Continuity costs no extra hypothesis in finite dimension. -/
noncomputable def continuousScreeningMultilinearForm
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) :=
  (continuousMultilinearOfFiniteDimensional m :
      MultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) →ₗ[ℂ]
        ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ))
    (screeningMultilinearForm adj rho T)

@[simp]
theorem continuousScreeningMultilinearForm_apply
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (v : Fin m → A) :
    continuousScreeningMultilinearForm adj rho T v =
      dualCoordinates n (T (PiTensorProduct.tprod ℂ v)) := by
  rw [continuousScreeningMultilinearForm,
    continuousMultilinearOfFiniteDimensional_apply]
  rfl

/-- The continuous form intertwines the diagonal source action with the
fixed-coordinate contragredient Wilson action. -/
theorem continuousScreeningMultilinearForm_equivariant
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (g : G) (v : Fin m → A) :
    continuousScreeningMultilinearForm adj rho T (fun i ↦ adj g (v i)) =
      representationAction (dualUnitaryRepData rho) g
        (continuousScreeningMultilinearForm adj rho T v) := by
  rw [continuousScreeningMultilinearForm_apply,
    continuousScreeningMultilinearForm_apply, ← tensorPower_tprod,
    T.isIntertwining, dualCoordinates_dual_action]

/-! ## Primal Wilson coordinates -/

/-- Evaluate a tensor-power screening intertwiner whose target is the Wilson
representation itself.  Unlike the legacy dual-coordinate construction
above, the output already is the desired coordinate vector. -/
noncomputable def representationScreeningMultilinearForm
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho)) :
    MultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) :=
  T.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ)

@[simp]
theorem representationScreeningMultilinearForm_apply
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho))
    (v : Fin m → A) :
    representationScreeningMultilinearForm adj rho T v =
      T (PiTensorProduct.tprod ℂ v) :=
  rfl

/-- The primal screening form, regarded as a continuous multilinear map.
Finite dimensionality supplies continuity exactly as in the legacy bridge. -/
noncomputable def continuousRepresentationScreeningMultilinearForm
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) :=
  (continuousMultilinearOfFiniteDimensional m :
      MultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ) →ₗ[ℂ]
        ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) (Fin n → ℂ))
    (representationScreeningMultilinearForm adj rho T)

@[simp]
theorem continuousRepresentationScreeningMultilinearForm_apply
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho))
    (v : Fin m → A) :
    continuousRepresentationScreeningMultilinearForm adj rho T v =
      T (PiTensorProduct.tprod ℂ v) := by
  rw [continuousRepresentationScreeningMultilinearForm,
    continuousMultilinearOfFiniteDimensional_apply]
  rfl

/-- The primal continuous form intertwines the diagonal source action with
the ordinary Wilson representation action. -/
theorem continuousRepresentationScreeningMultilinearForm_equivariant
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho))
    (g : G) (v : Fin m → A) :
    continuousRepresentationScreeningMultilinearForm adj rho T
        (fun i ↦ adj g (v i)) =
      representationAction rho g
        (continuousRepresentationScreeningMultilinearForm adj rho T v) := by
  rw [continuousRepresentationScreeningMultilinearForm_apply,
    continuousRepresentationScreeningMultilinearForm_apply,
    ← tensorPower_tprod, T.isIntertwining]
  rfl

/-! ## Pure-tensor detection from a spanning family -/

/-- A multilinear map which vanishes whenever every input belongs to a
spanning set is zero. -/
theorem multilinear_eq_zero_of_eq_zero_on_spanning
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Set V) (hspan : Submodule.span K S = ⊤) :
    ∀ {r : ℕ} (F : MultilinearMap K (fun _ : Fin r ↦ V) W),
      (∀ x : Fin r → V, (∀ i, x i ∈ S) → F x = 0) → F = 0 := by
  intro r
  induction r with
  | zero =>
      intro F hzero
      ext x
      exact hzero x (fun i ↦ Fin.elim0 i)
  | succ r ih =>
      intro F hzero
      have hcurried : F.curryLeft = 0 := by
        apply LinearMap.ext_on hspan
        intro v hv
        apply ih (F.curryLeft v)
        intro x hx
        rw [MultilinearMap.curryLeft_apply]
        apply hzero
        intro i
        refine Fin.cases hv ?_ i
        intro j
        simpa using hx j
      exact (multilinearCurryLeftEquiv
        (R := K) (M := fun _ : Fin (r + 1) ↦ V) (M₂ := W)).injective hcurried

/-- A nonzero linear map on a tensor power is nonzero on a pure tensor whose
factors come from any spanning family. -/
theorem nonzero_on_pure_tensor_of_spans
    {K V W I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {r : ℕ} (a : I → V)
    (T : (⨂[K]^r V) →ₗ[K] W) (hT : T ≠ 0)
    (hspan : Submodule.span K (Set.range a) = ⊤) :
    ∃ g : Fin r → I,
      T (PiTensorProduct.tprod K (fun i ↦ a (g i))) ≠ 0 := by
  by_contra h
  push_neg at h
  let F : MultilinearMap K (fun _ : Fin r ↦ V) W :=
    T.compMultilinearMap (PiTensorProduct.tprod K)
  have hF : F = 0 := by
    apply multilinear_eq_zero_of_eq_zero_on_spanning (Set.range a) hspan F
    intro x hx
    choose g hg using fun i ↦ hx i
    have hxa : x = fun i ↦ a (g i) := funext fun i ↦ (hg i).symm
    simpa [F, hxa] using h g
  apply hT
  apply PiTensorProduct.ext
  simpa [F] using hF

end

end YangMills.Gluelump.Endpoint
