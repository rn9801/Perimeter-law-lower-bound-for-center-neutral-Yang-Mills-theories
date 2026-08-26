/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Field
import GluelumpPerimeterLaw.OneLink.EndpointPolynomial
import GluelumpPerimeterLaw.OneLink.WordDetection

/-!
# Exact homogeneous mode of the comb endpoint

This file carries out the concrete algebraic part of all-coupling Milestone G.
The endpoint collar is a fixed finite set of positive edges.  Both an edge
matrix and the matrix of its reversed orientation are literal coordinates in
the doubled faithful feature family.  Consequently path holonomies, the real-
linear axial projection, and the multilinear screening map have exact finite
homogeneous expansions; no Stone--Weierstrass approximation is used.
-/

namespace YangMills.Gluelump.OneLink

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.Gluelump.Endpoint YangMills.Gluelump.RepresentationTheory
open Representation
open scoped Matrix ComplexConjugate BigOperators

noncomputable section

universe u

variable {d n : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## Doubled coordinates for a real-linear matrix map -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Coefficient of the unconjugated matrix entry in the complex
decomposition of a real-linear matrix map. -/
def realLinearMatrixCoeff (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] V)
    (i j : Fin n) : V :=
  (2 : ℂ)⁻¹ •
    (L (Matrix.single i j 1) -
      Complex.I • L (Complex.I • Matrix.single i j 1))

/-- Coefficient of the conjugated matrix entry in the complex decomposition
of a real-linear matrix map. -/
def realLinearMatrixConjCoeff (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] V)
    (i j : Fin n) : V :=
  (2 : ℂ)⁻¹ •
    (L (Matrix.single i j 1) +
      Complex.I • L (Complex.I • Matrix.single i j 1))

/-- Exact doubled-coordinate decomposition on a single matrix unit. -/
theorem realLinearMap_single_eq_doubled
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] V)
    (z : ℂ) (i j : Fin n) :
    L (Matrix.single i j z) =
      z • realLinearMatrixCoeff L i j +
        conj z • realLinearMatrixConjCoeff L i j := by
  have hmat : Matrix.single i j z =
      z.re • Matrix.single i j (1 : ℂ) +
        z.im • (Complex.I • Matrix.single i j (1 : ℂ)) := by
    ext a b
    simp only [Matrix.single_apply]
    split
    · rename_i h
      rcases h with ⟨rfl, rfl⟩
      simp [Complex.ext_iff, mul_comm]
    · rename_i h
      simp [h]
  rw [hmat, map_add, map_smul, map_smul]
  simp only [realLinearMatrixCoeff, realLinearMatrixConjCoeff]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) z.re,
    RCLike.real_smul_eq_coe_smul (K := ℂ) z.im]
  have hz : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp
  have hzi : (z.im : ℂ) = Complex.I * (conj z - z) / 2 := by
    apply Complex.ext <;> simp
  calc
    _ = ((z + conj z) / 2) • L (Matrix.single i j 1) +
        (Complex.I * (conj z - z) / 2) •
          L (Complex.I • Matrix.single i j 1) := by
      exact congrArg₂ (· + ·)
        (congrArg (fun c : ℂ ↦ c • L (Matrix.single i j 1)) hz)
        (congrArg (fun c : ℂ ↦
          c • L (Complex.I • Matrix.single i j 1)) hzi)
    _ = _ := by module

/-- Every real-linear map out of a finite complex matrix space is the sum of
an unconjugated and a conjugated complex matrix-coordinate map.  This is the
precise algebraic reason the doubled feature removes any complex-linearity
assumption on `FaithfulActionAxialData.projectBack`. -/
theorem realLinearMap_matrix_eq_doubled
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] V)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    L M = ∑ i, ∑ j,
      (M i j • realLinearMatrixCoeff L i j +
        conj (M i j) • realLinearMatrixConjCoeff L i j) := by
  classical
  have hM : M = ∑ i, ∑ j, Matrix.single i j (M i j) := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.single_apply]
    rw [Fintype.sum_eq_single a]
    · rw [Fintype.sum_eq_single b]
      · simp
      · intro b' hne
        simp [hne]
    · intro a' hne
      simp [hne]
  calc
    L M = L (∑ i, ∑ j, Matrix.single i j (M i j)) := congrArg L hM
    _ = ∑ i, ∑ j, L (Matrix.single i j (M i j)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      exact realLinearMap_single_eq_doubled L (M i j) i j

/-- The doubled matrix-feature letter read by one oriented edge occurrence.
For a backward occurrence the matrix indices are transposed because a unitary
inverse is the conjugate transpose. -/
def signedEdgeFeatureLetter (S : Finset (PositiveEdge d))
    (e : SignedEdge d) (he : e.positive ∈ S) (i j : Fin n) :
    MatrixFeatureLetter S n :=
  match h : e.direction.orientation with
  | .forward => (⟨e.positive, he⟩, false, i, j)
  | .backward => (⟨e.positive, he⟩, true, j, i)

/-- Every represented oriented edge is exactly one doubled feature
coordinate on the finite collar. -/
theorem represented_signedEdgeValue_eq_matrixFeature
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) (e : SignedEdge d)
    (he : e.positive ∈ S) (i j : Fin n) (U : S → G) :
    (sigma.ρ (signedEdgeValue (extendFromFinset S U) e) :
        Matrix (Fin n) (Fin n) ℂ) i j =
      matrixFeature sigma (signedEdgeFeatureLetter S e he i j) U := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward =>
              change (⟨source, axis⟩ : PositiveEdge d) ∈ S at he
              simp only [signedEdgeFeatureLetter, signedEdgeValue,
                SignedEdge.positive, extendFromFinset, matrixFeature]
              rw [dif_pos he]
              rfl
          | backward =>
              change (⟨step source (.backward axis), axis⟩ :
                PositiveEdge d) ∈ S at he
              simp only [signedEdgeFeatureLetter, signedEdgeValue,
                SignedEdge.positive, SignedEdge.target, map_inv,
                Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
                Matrix.conjTranspose_apply, matrixFeature]
              change star
                  ((sigma.ρ (extendFromFinset S U
                    ⟨step source (.backward axis), axis⟩) :
                      Matrix (Fin n) (Fin n) ℂ) j i) =
                star ((sigma.ρ (U
                  ⟨⟨step source (.backward axis), axis⟩, he⟩) :
                    Matrix (Fin n) (Fin n) ℂ) j i)
              rw [show extendFromFinset S U
                  ⟨step source (.backward axis), axis⟩ =
                    U ⟨⟨step source (.backward axis), axis⟩, he⟩ by
                unfold extendFromFinset
                rw [dif_pos he]]

/-! ## Exact path-holonomy degree -/

/-- One represented matrix entry of a path holonomy after extending a collar
configuration by the identity. -/
def representedHolonomyEntry (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (i j : Fin n) : C(S → G, ℂ) where
  toFun U :=
    (sigma.ρ (holonomy (extendFromFinset S U) p) :
      Matrix (Fin n) (Fin n) ℂ) i j
  continuous_toFun := by
    have hext : Continuous (extendFromFinset S : (S → G) → Configuration d G) := by
      apply continuous_pi
      intro a
      unfold extendFromFinset
      split
      · exact continuous_apply _
      · exact continuous_const
    exact (continuous_apply j).comp <| (continuous_apply i).comp <|
      continuous_subtype_val.comp <| sigma.continuous_ρ.comp <|
        (continuous_holonomy p).comp hext

@[simp]
theorem representedHolonomyEntry_apply
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (i j : Fin n) (U : S → G) :
    representedHolonomyEntry sigma S p i j U =
      (sigma.ρ (holonomy (extendFromFinset S U) p) :
        Matrix (Fin n) (Fin n) ℂ) i j :=
  rfl

/-- A path-holonomy matrix entry is exactly homogeneous of degree the number
of oriented edge occurrences.  Repeated stored edges cause no problem: every
occurrence uses the same coordinate in the fixed collar feature family. -/
noncomputable def representedHolonomyEntry_homogeneous
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (hp : p.edgeSupport ⊆ S)
    (i j : Fin n) :
    HomogeneousFeatureExpansion (matrixFeature sigma) p.length
      (representedHolonomyEntry sigma S p i j) := by
  induction p generalizing i j with
  | nil =>
      let c : ℂ := if i = j then 1 else 0
      refine (HomogeneousFeatureExpansion.constant
        (matrixFeature sigma) c).congr ?_
      ext U
      simp [representedHolonomyEntry, c, Matrix.one_apply]
  | @cons z w p e ih =>
      have hp' : Lattice.Cubic.Path.edgeSupport p ⊆ S := by
        intro a ha
        apply hp
        rw [Lattice.Cubic.Path.edgeSupport_cons]
        exact Finset.mem_insert_of_mem ha
      have he : e.1.positive ∈ S := by
        apply hp
        rw [Lattice.Cubic.Path.edgeSupport_cons]
        exact Finset.mem_insert_self _ _
      let term : Fin n → C(S → G, ℂ) := fun k ↦
        representedHolonomyEntry sigma S p i k *
          matrixFeature sigma
            (signedEdgeFeatureLetter S e.1 he k j)
      have hterm (k : Fin n) :
          HomogeneousFeatureExpansion (matrixFeature sigma)
            (p.length + 1) (term k) :=
        HomogeneousFeatureExpansion.mul (ih hp' i k)
          (HomogeneousFeatureExpansion.coordinate
            (signedEdgeFeatureLetter S e.1 he k j))
      refine (HomogeneousFeatureExpansion.sum term hterm).congr ?_
      ext U
      simp only [term, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
        representedHolonomyEntry_apply, holonomy_cons, map_mul,
        Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [represented_signedEdgeValue_eq_matrixFeature sigma S e.1 he k j U]

/-- Flipping the Boolean orientation twice returns the original doubled
matrix-feature letter. -/
theorem matrixFeatureLetter_flip_involutive
    (S : Finset (PositiveEdge d)) :
    Function.Involutive
      (MatrixFeatureLetter.flip : MatrixFeatureLetter S n →
        MatrixFeatureLetter S n) := by
  intro a
  rcases a with ⟨e, b, i, j⟩
  cases b <;> rfl

/-- Conjugating a homogeneous collar function preserves its degree in the
doubled matrix-feature family. -/
noncomputable def matrixFeatureExpansion_star
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {r : ℕ} {f : C(S → G, ℂ)}
    (hf : HomogeneousFeatureExpansion (matrixFeature sigma) r f) :
    HomogeneousFeatureExpansion (matrixFeature sigma) r (Star.star f) :=
  HomogeneousFeatureExpansion.star MatrixFeatureLetter.flip
    (matrixFeatureLetter_flip_involutive S)
    (matrixFeature_flip sigma) hf

/-- The represented axial-matrix entry, written directly in doubled collar
coordinates. -/
def representedAxialMatrixEntry (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (i j : Fin n) : C(S → G, ℂ) :=
  (2 : ℂ)⁻¹ •
    (representedHolonomyEntry sigma S p i j -
      Star.star (representedHolonomyEntry sigma S p j i))

@[simp]
theorem representedAxialMatrixEntry_apply
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (i j : Fin n) (U : S → G) :
    representedAxialMatrixEntry sigma S p i j U =
      YangMills.Gluelump.Lie.axialMatrix sigma
        (holonomy (extendFromFinset S U) p) i j := by
  simp only [representedAxialMatrixEntry, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, representedHolonomyEntry_apply,
    ContinuousMap.star_apply, starRingEnd_apply]
  unfold YangMills.Gluelump.Lie.axialMatrix
  simp only [smul_eq_mul, Matrix.smul_apply, Matrix.sub_apply, map_inv,
    Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply]

/-- An axial-matrix entry remains exactly homogeneous of the path length.
This combines the path theorem with doubled-feature closure under
conjugation. -/
noncomputable def representedAxialMatrixEntry_homogeneous
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (hp : p.edgeSupport ⊆ S)
    (i j : Fin n) :
    HomogeneousFeatureExpansion (matrixFeature sigma) p.length
      (representedAxialMatrixEntry sigma S p i j) := by
  let hij := representedHolonomyEntry_homogeneous sigma S p hp i j
  let hjiStar := matrixFeatureExpansion_star sigma S
    (representedHolonomyEntry_homogeneous sigma S p hp j i)
  let hneg := HomogeneousFeatureExpansion.smul (-1 : ℂ) hjiStar
  let hsub := HomogeneousFeatureExpansion.add hij hneg
  let hscaled := HomogeneousFeatureExpansion.smul ((2 : ℂ)⁻¹) hsub
  refine hscaled.congr ?_
  ext U
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.star_apply, representedHolonomyEntry_apply,
    representedAxialMatrixEntry, ContinuousMap.sub_apply]
  ring

/-! ## Scalar coordinates of the generalized axial map -/

variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [FiniteDimensional ℂ A]

/-- A scalar coordinate of the generalized axial value of a represented path
holonomy on the fixed collar. -/
def representedGeneralizedAxialCoordinate
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (ell : A →L[ℂ] ℂ) : C(S → G, ℂ) where
  toFun U := ell (YangMills.Gluelump.Lie.generalizedAxial D
    (holonomy (extendFromFinset S U) p))
  continuous_toFun := by
    have hext : Continuous (extendFromFinset S : (S → G) → Configuration d G) := by
      apply continuous_pi
      intro a
      unfold extendFromFinset
      split
      · exact continuous_apply _
      · exact continuous_const
    exact ell.continuous.comp <|
      (YangMills.Gluelump.Lie.continuous_generalizedAxial D).comp <|
        (continuous_holonomy p).comp hext

@[simp]
theorem representedGeneralizedAxialCoordinate_apply
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (ell : A →L[ℂ] ℂ) (U : S → G) :
    representedGeneralizedAxialCoordinate D S p ell U =
      ell (YangMills.Gluelump.Lie.generalizedAxial D
        (holonomy (extendFromFinset S U) p)) :=
  rfl

/-- Every scalar coordinate of the generalized axial path value is exactly
homogeneous of the path length.  The proof uses the explicit doubled
decomposition of the real-linear `projectBack`; no complex-linearity of that
map is assumed. -/
noncomputable def representedGeneralizedAxialCoordinate_homogeneous
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (p : Lattice.Cubic.Path x y) (hp : p.edgeSupport ⊆ S)
    (ell : A →L[ℂ] ℂ) :
    HomogeneousFeatureExpansion (matrixFeature D.sigma) p.length
      (representedGeneralizedAxialCoordinate D S p ell) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    ((ell : A →ₗ[ℂ] ℂ).restrictScalars ℝ).comp D.projectBack
  let axialEntry : Fin n → Fin n → C(S → G, ℂ) := fun i j ↦
    representedAxialMatrixEntry D.sigma S p i j
  let term : Fin n → Fin n → C(S → G, ℂ) := fun i j ↦
    realLinearMatrixCoeff L i j • axialEntry i j +
      realLinearMatrixConjCoeff L i j • Star.star (axialEntry i j)
  have haxial (i j : Fin n) :
      HomogeneousFeatureExpansion (matrixFeature D.sigma) p.length
        (axialEntry i j) :=
    representedAxialMatrixEntry_homogeneous D.sigma S p hp i j
  have hterm (i j : Fin n) :
      HomogeneousFeatureExpansion (matrixFeature D.sigma) p.length
        (term i j) :=
    HomogeneousFeatureExpansion.add
      (HomogeneousFeatureExpansion.smul (realLinearMatrixCoeff L i j)
        (haxial i j))
      (HomogeneousFeatureExpansion.smul (realLinearMatrixConjCoeff L i j)
        (matrixFeatureExpansion_star D.sigma S (haxial i j)))
  let row : Fin n → C(S → G, ℂ) := fun i ↦ ∑ j, term i j
  have hrow (i : Fin n) :
      HomogeneousFeatureExpansion (matrixFeature D.sigma) p.length (row i) :=
    HomogeneousFeatureExpansion.sum (fun j ↦ term i j) (hterm i)
  let htotal : HomogeneousFeatureExpansion (matrixFeature D.sigma) p.length
      (∑ i, row i) :=
    HomogeneousFeatureExpansion.sum row hrow
  refine htotal.congr ?_
  ext U
  simp only [row, term, ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, ContinuousMap.star_apply, axialEntry,
    representedAxialMatrixEntry_apply,
    representedGeneralizedAxialCoordinate_apply]
  let M := YangMills.Gluelump.Lie.axialMatrix D.sigma
    (holonomy (extendFromFinset S U) p)
  calc
    (∑ i, ∑ j, (
        (realLinearMatrixCoeff L i j) * M i j +
          (realLinearMatrixConjCoeff L i j) * conj (M i j))) =
        ∑ i, ∑ j,
          (M i j • realLinearMatrixCoeff L i j +
            conj (M i j) • realLinearMatrixConjCoeff L i j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [smul_eq_mul]
      ring
    _ = L M := (realLinearMap_matrix_eq_doubled L M).symm
    _ = ell (YangMills.Gluelump.Lie.generalizedAxial D
        (holonomy (extendFromFinset S U) p)) := rfl

/-! ## Multilinear screening coordinates -/

/-- The canonical continuous coordinate functional associated to the fixed
finite basis of the generalized axial space. -/
def axialFinBasisCoordinate (k : Fin (Module.finrank ℂ A)) : A →L[ℂ] ℂ :=
  ⟨(Module.finBasis ℂ A).coord k,
    (Module.finBasis ℂ A).coord k |>.continuous_of_finiteDimensional⟩

/-- Apply a scalar continuous multilinear form to the generalized axial
values of a finite family of represented collar holonomies. -/
def representedGeneralizedAxialMultilinear
    {m : ℕ} (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) ℂ) :
    C(S → G, ℂ) where
  toFun U := F (fun j ↦ YangMills.Gluelump.Lie.generalizedAxial D
    (holonomy (extendFromFinset S U) (q j)))
  continuous_toFun := by
    apply F.cont.comp
    apply continuous_pi
    intro j
    exact (YangMills.Gluelump.Lie.continuous_generalizedAxial D).comp <|
      (continuous_holonomy (q j)).comp (continuous_extendFromFinset S)

@[simp]
theorem representedGeneralizedAxialMultilinear_apply
    {m : ℕ} (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) ℂ)
    (U : S → G) :
    representedGeneralizedAxialMultilinear D S q F U =
      F (fun j ↦ YangMills.Gluelump.Lie.generalizedAxial D
        (holonomy (extendFromFinset S U) (q j))) :=
  rfl

/-- Expanding every axial input in the canonical finite basis and then using
multilinearity gives an exact homogeneous feature expansion.  This is the
coordinate-level tensor argument needed for the comb endpoint. -/
noncomputable def representedGeneralizedAxialMultilinear_homogeneous
    {m : ℕ} (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (hq : ∀ j, (q j).edgeSupport ⊆ S)
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) ℂ) :
    HomogeneousFeatureExpansion (matrixFeature D.sigma)
      (∑ j, (q j).length)
      (representedGeneralizedAxialMultilinear D S q F) := by
  let b := Module.finBasis ℂ A
  let coordinate : Fin m → Fin (Module.finrank ℂ A) → C(S → G, ℂ) :=
    fun j k ↦ representedGeneralizedAxialCoordinate D S (q j)
      (axialFinBasisCoordinate k)
  have hcoordinate (j : Fin m) (k : Fin (Module.finrank ℂ A)) :
      HomogeneousFeatureExpansion (matrixFeature D.sigma) (q j).length
        (coordinate j k) :=
    representedGeneralizedAxialCoordinate_homogeneous D S (q j) (hq j)
      (axialFinBasisCoordinate k)
  let term : (Fin m → Fin (Module.finrank ℂ A)) → C(S → G, ℂ) :=
    fun ks ↦ F (fun j ↦ b (ks j)) • ∏ j, coordinate j (ks j)
  have hterm (ks : Fin m → Fin (Module.finrank ℂ A)) :
      HomogeneousFeatureExpansion (matrixFeature D.sigma)
        (∑ j, (q j).length) (term ks) :=
    HomogeneousFeatureExpansion.smul (F (fun j ↦ b (ks j))) <|
      HomogeneousFeatureExpansion.finProduct (fun j ↦ (q j).length)
        (fun j ↦ coordinate j (ks j)) (fun j ↦ hcoordinate j (ks j))
  let hsum : HomogeneousFeatureExpansion (matrixFeature D.sigma)
      (∑ j, (q j).length) (∑ ks, term ks) :=
    HomogeneousFeatureExpansion.sum term hterm
  refine hsum.congr ?_
  ext U
  let v : Fin m → A := fun j ↦ YangMills.Gluelump.Lie.generalizedAxial D
    (holonomy (extendFromFinset S U) (q j))
  have hv (j : Fin m) : ∑ k, b.repr (v j) k • b k = v j := b.sum_repr (v j)
  calc
    (∑ ks : Fin m → Fin (Module.finrank ℂ A), term ks) U =
        ∑ ks : Fin m → Fin (Module.finrank ℂ A), F (fun j ↦ b (ks j)) *
          ∏ j, b.repr (v j) (ks j) := by
      simp only [ContinuousMap.sum_apply]
      apply Finset.sum_congr rfl
      intro (ks : Fin m → Fin (Module.finrank ℂ A)) _hks
      simp only [term, ContinuousMap.smul_apply, ContinuousMap.prod_apply,
        coordinate, representedGeneralizedAxialCoordinate_apply, smul_eq_mul,
        axialFinBasisCoordinate, ContinuousLinearMap.coe_mk',
        Module.Basis.coord, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Finsupp.lapply_apply, v]
      dsimp only [b]
    _ = ∑ ks : Fin m → Fin (Module.finrank ℂ A),
        F (fun j ↦ b.repr (v j) (ks j) • b (ks j)) := by
      apply Finset.sum_congr rfl
      intro (ks : Fin m → Fin (Module.finrank ℂ A)) _hks
      rw [F.map_smul_univ]
      simp only [smul_eq_mul]
      ring
    _ = F (fun j ↦ ∑ k, b.repr (v j) k • b k) := by
      exact (F.map_sum fun j k ↦ b.repr (v j) k • b k).symm
    _ = F v := by congr 1; funext j; exact hv j
    _ = representedGeneralizedAxialMultilinear D S q F U := rfl

/-! ## The concrete normalized comb mode -/

/-- The fixed positive-edge collar read by the comb endpoint. -/
def combEndpointCollar {m : ℕ} (hd : 3 ≤ d) (x : Site d) :
    Finset (PositiveEdge d) :=
  basedLoopSupport (combLoops (m := m) hd x)

/-- The exact homogeneous degree of the comb screening endpoint.  It counts
oriented edge occurrences, including repetitions, in all comb loops. -/
def combEndpointDegree {m : ℕ} (hd : 3 ≤ d) (x : Site d) : ℕ :=
  ∑ j : Fin m, (combLoops hd x j).length

/-- The collar restriction of one coordinate of the normalized comb
endpoint. -/
def combPhiCollarCoordinate {m r : ℕ} (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (i : Fin r) : C(combEndpointCollar (m := m) hd x → G, ℂ) :=
  collarRestriction (combEndpointCollar (m := m) hd x)
    ((phi hd D adj rho T x).component i).toContinuousMap

/-- Every normalized comb coordinate has the same exact homogeneous degree.
Normalization contributes one fixed positive scalar and therefore does not
alter the degree. -/
noncomputable def combPhiCollarCoordinate_homogeneous
    {m r : ℕ} (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (i : Fin r) :
    HomogeneousFeatureExpansion (matrixFeature D.sigma)
      (combEndpointDegree (m := m) hd x)
      (combPhiCollarCoordinate hd D adj rho T x i) := by
  let S := combEndpointCollar (m := m) hd x
  let q := combLoops (m := m) hd x
  let F : ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ A) ℂ :=
    (ContinuousLinearMap.proj i).compContinuousMultilinearMap
      (continuousScreeningMultilinearForm adj rho T)
  have hq (j : Fin m) : (q j).edgeSupport ⊆ S := by
    intro e he
    change e ∈ basedLoopSupport q
    rw [basedLoopSupport, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ j, he⟩
  let hraw := representedGeneralizedAxialMultilinear_homogeneous
    D S q hq F
  let hscaled := HomogeneousFeatureExpansion.smul
    (endpointNormalizationScale
      (generalizedAxialTensorField D q
        (continuousScreeningMultilinearForm adj rho T)) : ℂ) hraw
  refine hscaled.congr ?_
  ext U
  simp only [ContinuousMap.smul_apply,
    representedGeneralizedAxialMultilinear_apply,
    combPhiCollarCoordinate, collarRestriction, ContinuousMap.comp_apply,
    LocalField.component_apply, phi, normalizedEndpoint_apply,
    generalizedAxialTensorField_apply, F,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
    ContinuousMap.coe_mk]
  dsimp only [S, q]

/-- Some normalized comb coordinate remains nonzero after restriction to the
exact collar.  This is proved from the existing explicit comb witness and
the recorded local-field dependency, without adding measure-theoretic
hypotheses. -/
theorem exists_combPhiCollarCoordinate_ne_zero
    {m r : ℕ} (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (H : YangMills.Gluelump.Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d) :
    ∃ i : Fin r, combPhiCollarCoordinate hd D adj rho T x i ≠ 0 := by
  obtain ⟨Q, hQ⟩ := phi_not_identically_zero hd D H adj rho T hT x
  obtain ⟨i, hi⟩ : ∃ i : Fin r, phi hd D adj rho T x Q i ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (funext h)
  refine ⟨i, ?_⟩
  intro hzero
  let S := combEndpointCollar (m := m) hd x
  let V : S → G := restrictToFinset S Q
  have hvalue : combPhiCollarCoordinate hd D adj rho T x i V =
      phi hd D adj rho T x Q i := by
    exact ((phi hd D adj rho T x).component i).dependsOn_support
      (fun e he ↦ extendFromFinset_restrictToFinset_apply S Q e (by
        simpa [S, combEndpointCollar] using he))
  have hz := DFunLike.congr_fun hzero V
  simp only [ContinuousMap.zero_apply] at hz
  exact hi (hvalue ▸ hz)

/-- The concrete normalized comb endpoint supplies the exact nonzero
conjugate mode required by the abstract all-coupling extraction chain. -/
noncomputable def combEndpointConjugateMode
    {m r : ℕ} (hd : 3 ≤ d)
    (D : YangMills.Gluelump.Lie.FaithfulActionAxialData G A n)
    (H : YangMills.Gluelump.Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d) :
    EndpointConjugateMode (matrixFeature D.sigma)
      (fun i ↦ combPhiCollarCoordinate hd D adj rho T x i)
      (combEndpointDegree (m := m) hd x) := by
  let hex := exists_combPhiCollarCoordinate_ne_zero hd D H adj rho T hT x
  let i := Classical.choose hex
  have hi : combPhiCollarCoordinate hd D adj rho T x i ≠ 0 :=
    Classical.choose_spec hex
  let hhom := combPhiCollarCoordinate_homogeneous hd D adj rho T x i
  let hstar := matrixFeatureExpansion_star D.sigma
    (combEndpointCollar (m := m) hd x) hhom
  exact EndpointConjugateMode.ofCoordinate (matrixFeature D.sigma)
    (fun j ↦ combPhiCollarCoordinate hd D adj rho T x j) i
    hstar.coefficient hi (fun U ↦ by simpa using hstar.expansion U)

/-- Transport a doubled-matrix endpoint mode across a finite coordinate
reindexing.  Both the endpoint functions and their feature labels are moved,
so the resulting mode is stated in the target coordinate model literally. -/
noncomputable def reindexMatrixEndpointMode
    {J K O : Type*} [Fintype J] [Fintype K] [Fintype O]
    (sigma : ContinuousUnitaryRepData G n) (e : J ≃ K)
    (Phi : O → C(J → G, ℂ)) {degree : ℕ}
    (mode : EndpointConjugateMode (matrixFeature sigma) Phi degree) :
    EndpointConjugateMode (matrixFeature sigma)
      (fun i ↦ (Phi i).comp
        ⟨fun U j ↦ U (e j), by
          apply continuous_pi
          intro j
          exact continuous_apply (e j)⟩) degree := by
  let pull : C((K → G), (J → G)) :=
    ⟨fun U j ↦ U (e j), by
      apply continuous_pi
      intro j
      exact continuous_apply (e j)⟩
  have hpull : Function.Surjective pull := by
    intro V
    refine ⟨fun k ↦ V (e.symm k), ?_⟩
    funext j
    simp [pull]
  let pulled := mode.compDomain pull hpull
  let embed : MatrixFeatureLetter J n → MatrixFeatureLetter K n :=
    fun a ↦ (e a.1, a.2.1, a.2.2.1, a.2.2.2)
  have hfeature (a : MatrixFeatureLetter J n) :
      matrixFeature sigma (embed a) = (matrixFeature sigma a).comp pull := by
    ext U
    rcases a with ⟨j, b, r, s⟩
    rfl
  exact pulled.mapFeature (matrixFeature sigma) embed hfeature

end

end YangMills.Gluelump.OneLink
