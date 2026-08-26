/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Lie.AxialMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Generalized axial map from a faithful action representation

This is the representation-independent part of roadmap Milestone B.  The
matrix odd part is projected back to the real Lie algebra by the inverse of
the faithful infinitesimal action after orthogonal projection.  Until the
missing Lie-group differential API is supplied, that projected inverse and
its conjugation covariance are explicit data rather than a hidden axiom.

No lattice object occurs in this file.
-/

namespace YangMills.Gluelump.Lie

open YangMills.Wilson Representation
open scoped Matrix Topology TensorProduct

noncomputable section

universe u

variable {G 𝔤 : Type u} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]

/-- The faithful action representation together with the conjugation-
equivariant projected inverse of its differential.  In the intended
specialization `projectBack` is

`(d sigma)^{-1} ∘ P_sigma : End_C(S)_R → 𝔤`.

The construction and covariance of this map form the fourth explicit
temporary assumption interface in the general development. -/
structure FaithfulActionAxialData (G 𝔤 : Type u) (n : ℕ)
    [Group G] [TopologicalSpace G]
    [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] where
  /-- The faithful unitary action representation used by the Wilson action. -/
  sigma : ContinuousUnitaryRepData G n
  /-- Faithfulness of the action representation. -/
  faithful : Function.Injective sigma.ρ
  /-- The real adjoint action on the Lie algebra. -/
  adjoint : Representation ℝ G 𝔤
  /-- Orthogonal projection to `range (d sigma)`, followed by its inverse. -/
  projectBack : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] 𝔤
  /-- Conjugation covariance of the orthogonal projection and inverse. -/
  projectBack_conj (h : G) (A : Matrix (Fin n) (Fin n) ℂ) :
    projectBack
        ((sigma.ρ h : Matrix (Fin n) (Fin n) ℂ) * A *
          (sigma.ρ h⁻¹ : Matrix (Fin n) (Fin n) ℂ)) =
      adjoint h (projectBack A)

/-- The generalized Cayley/log-like axial map associated with a faithful
action representation. -/
def generalizedAxial (D : FaithfulActionAxialData G 𝔤 n) (g : G) : 𝔤 :=
  D.projectBack (axialMatrix D.sigma g)

/-- Continuity of the generalized axial map. -/
theorem continuous_generalizedAxial (D : FaithfulActionAxialData G 𝔤 n) :
    Continuous (generalizedAxial D) :=
  D.projectBack.continuous_of_finiteDimensional.comp
    (continuous_axialMatrix D.sigma)

/-- The generalized axial map vanishes at the identity. -/
@[simp]
theorem generalizedAxial_one (D : FaithfulActionAxialData G 𝔤 n) :
    generalizedAxial D 1 = 0 := by
  simp [generalizedAxial]

/-- The generalized axial map is odd under inversion. -/
theorem generalizedAxial_inv (D : FaithfulActionAxialData G 𝔤 n) (g : G) :
    generalizedAxial D g⁻¹ = -generalizedAxial D g := by
  simp [generalizedAxial, axialMatrix_inv]

/-- Conjugation covariance under the real adjoint action. -/
theorem generalizedAxial_conj (D : FaithfulActionAxialData G 𝔤 n)
    (h g : G) :
    generalizedAxial D (h * g * h⁻¹) =
      D.adjoint h (generalizedAxial D g) := by
  rw [generalizedAxial, axialMatrix_conj, D.projectBack_conj]
  rfl

/-- Compactness gives a uniform norm bound for the generalized axial map. -/
theorem generalizedAxial_bounded [CompactSpace G]
    (D : FaithfulActionAxialData G 𝔤 n) :
    ∃ C : ℝ, ∀ g : G, ‖generalizedAxial D g‖ ≤ C := by
  have hbounded : Bornology.IsBounded (Set.range (generalizedAxial D)) :=
    (isCompact_range (continuous_generalizedAxial D)).isBounded
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      ∀ x ∈ Set.range (generalizedAxial D), ‖x‖ ≤ C :=
    hbounded.exists_norm_le
  exact ⟨C, fun g ↦ hC (generalizedAxial D g) ⟨g, rfl⟩⟩

/-! ## First order behavior and spanning -/

/-- Sequential form of `d(a_sigma)_1 = id`.  The sequence uses
`t_k = 1/(k+1)` and is equivalent to the usual derivative statement in the
finite-dimensional Lie algebra.  Supplying the exponential map and this
first-order calculation is the fifth and final temporary assumption interface
allowed by the general development. -/
structure AxialFirstOrderData (D : FaithfulActionAxialData G 𝔤 n) where
  /-- The Lie-group exponential map. -/
  expMap : 𝔤 → G
  /-- The exponential sends zero to the identity. -/
  expMap_zero : expMap 0 = 1
  /-- Difference quotients of the generalized axial map converge to the
  original tangent vector. -/
  firstOrder (X : 𝔤) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ((k + 1 : ℕ) : ℝ) •
          generalizedAxial D
            (expMap ((((k + 1 : ℕ) : ℝ)⁻¹) • X)))
      Filter.atTop (𝓝 X)

/-- The isolated derivative-at-identity statement. -/
theorem generalizedAxial_firstOrder
    (D : FaithfulActionAxialData G 𝔤 n) (H : AxialFirstOrderData D)
    (X : 𝔤) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ((k + 1 : ℕ) : ℝ) •
          generalizedAxial D
            (H.expMap ((((k + 1 : ℕ) : ℝ)⁻¹) • X)))
      Filter.atTop (𝓝 X) :=
  H.firstOrder X

/-- The generalized axial values span the real Lie algebra.  This is the
finite-dimensional closed-subspace argument from the roadmap, applied to the
first-order sequence. -/
theorem span_range_generalizedAxial_eq_top
    (D : FaithfulActionAxialData G 𝔤 n) (H : AxialFirstOrderData D) :
    Submodule.span ℝ (Set.range (generalizedAxial D)) = ⊤ := by
  let L : Submodule ℝ 𝔤 :=
    Submodule.span ℝ (Set.range (generalizedAxial D))
  apply Submodule.eq_top_iff'.mpr
  intro X
  apply L.closed_of_finiteDimensional.mem_of_tendsto (H.firstOrder X)
  filter_upwards with k
  apply L.smul_mem
  exact Submodule.subset_span ⟨H.expMap
    ((((k + 1 : ℕ) : ℝ)⁻¹) • X), rfl⟩

/-! ## Pure-tensor nonvanishing -/

/-- A multilinear map which vanishes whenever every input belongs to a
spanning set is zero. -/
theorem multilinear_eq_zero_of_eq_zero_on_spanning
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Set V) (hspan : Submodule.span K S = ⊤) :
    ∀ {m : ℕ} (F : MultilinearMap K (fun _ : Fin m ↦ V) W),
      (∀ x : Fin m → V, (∀ i, x i ∈ S) → F x = 0) → F = 0 := by
  intro m
  induction m with
  | zero =>
      intro F hzero
      ext x
      exact hzero x (fun i ↦ Fin.elim0 i)
  | succ m ih =>
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
        (R := K) (M := fun _ : Fin (m + 1) ↦ V) (M₂ := W)).injective hcurried

/-- A nonzero linear map on a tensor power is nonzero on a pure tensor whose
factors come from any spanning family. -/
theorem nonzero_on_pure_tensor_of_spans
    {K V W I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {m : ℕ} (a : I → V)
    (T : (⨂[K]^m V) →ₗ[K] W) (hT : T ≠ 0)
    (hspan : Submodule.span K (Set.range a) = ⊤) :
    ∃ g : Fin m → I,
      T (PiTensorProduct.tprod K (fun i ↦ a (g i))) ≠ 0 := by
  by_contra h
  push_neg at h
  let F : MultilinearMap K (fun _ : Fin m ↦ V) W :=
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

end YangMills.Gluelump.Lie
