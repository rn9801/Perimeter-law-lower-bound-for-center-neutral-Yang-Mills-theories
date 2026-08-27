/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ConjugationSpanField
import GluelumpPerimeterLaw.OneLink.EndpointCombMode

/-!
# Exact homogeneous mode of the direct conjugation-span endpoint

This file reuses the proved doubled matrix-feature and fixed-degree
homogeneous-expansion infrastructure.  The only new input is the literal
matrix `sigma(holonomy)`, transported to its Hilbert--Schmidt conjugation-span
copy.  Thus the degree is exactly the total number of oriented occurrences
in the comb loops, and conjugation is handled by the explicit doubled-feature
flip rather than by Stone--Weierstrass approximation.
-/

namespace YangMills.Gluelump.OneLink

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.Gluelump.Endpoint YangMills.Gluelump.RepresentationTheory
open Representation
open scoped Matrix ComplexConjugate BigOperators

noncomputable section

universe u

variable {d n p : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## Explicit doubled feature conjugation -/

/-- Matrix-level doubled feature space `M ⊕ M`. -/
abbrev DoubledMatrix (n : ℕ) :=
  Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ

/-- The doubled feature `(sigma(g), sigma(g)ᴴ)`. -/
def doubledMatrixFeature (sigma : ContinuousUnitaryRepData G n) (g : G) :
    DoubledMatrix n :=
  (sigma.ρ g, (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ)ᴴ)

/-- The complex-linear swap-transpose map `J(A,B) = (Bᵀ,Aᵀ)`. -/
def doubledSwapTranspose (n : ℕ) :
    DoubledMatrix n →ₗ[ℂ] DoubledMatrix n where
  toFun AB := (AB.2ᵀ, AB.1ᵀ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On the doubled feature locus, swap-transpose is coordinatewise complex
conjugation.  This is the explicit linearization of the conjugation used by
the endpoint mode. -/
theorem doubledSwapTranspose_feature
    (sigma : ContinuousUnitaryRepData G n) (g : G) :
    doubledSwapTranspose n (doubledMatrixFeature sigma g) =
      ((sigma.ρ g : Matrix (Fin n) (Fin n) ℂ).map star,
        (sigma.ρ g : Matrix (Fin n) (Fin n) ℂ)ᵀ) := by
  ext i j <;>
    simp [doubledSwapTranspose, doubledMatrixFeature,
      Matrix.conjTranspose_apply]

/-! ## Scalar coordinates of literal holonomy matrices -/

/-- Extend a linear coordinate on the Hilbert conjugation-span subtype to
the ambient Hilbert matrix space. -/
def hilbertConjSpanCoordinateExtension
    (sigma : ContinuousUnitaryRepData G n)
    (ell : HilbertConjSpan sigma →L[ℂ] ℂ) : HilbertMatrix n →ₗ[ℂ] ℂ :=
  Classical.choose (LinearMap.exists_extend ell.toLinearMap)

@[simp]
theorem hilbertConjSpanCoordinateExtension_apply
    (sigma : ContinuousUnitaryRepData G n)
    (ell : HilbertConjSpan sigma →L[ℂ] ℂ)
    (A : HilbertConjSpan sigma) :
    hilbertConjSpanCoordinateExtension sigma ell A = ell A := by
  have h := Classical.choose_spec (LinearMap.exists_extend ell.toLinearMap)
  exact LinearMap.congr_fun h A

/-- One scalar coordinate of the represented literal holonomy matrix. -/
def representedHilbertConjSpanCoordinate
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (q : Lattice.Cubic.Path x y)
    (ell : HilbertConjSpan sigma →L[ℂ] ℂ) : C(S → G, ℂ) where
  toFun U := ell (sigmaInHilbertConjSpan sigma
    (holonomy (extendFromFinset S U) q))
  continuous_toFun :=
    ell.continuous.comp <| (continuous_sigmaInHilbertConjSpan sigma).comp <|
      (continuous_holonomy q).comp (continuous_extendFromFinset S)

@[simp]
theorem representedHilbertConjSpanCoordinate_apply
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (q : Lattice.Cubic.Path x y)
    (ell : HilbertConjSpan sigma →L[ℂ] ℂ) (U : S → G) :
    representedHilbertConjSpanCoordinate sigma S q ell U =
      ell (sigmaInHilbertConjSpan sigma
        (holonomy (extendFromFinset S U) q)) :=
  rfl

/-- Every linear coordinate of a literal represented path holonomy is
exactly homogeneous of degree `q.length` in the doubled feature family. -/
noncomputable opaque representedHilbertConjSpanCoordinate_homogeneous
    (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x y : Site d}
    (q : Lattice.Cubic.Path x y) (hq : q.edgeSupport ⊆ S)
    (ell : HilbertConjSpan sigma →L[ℂ] ℂ) :
    HomogeneousFeatureExpansion (matrixFeature sigma) q.length
      (representedHilbertConjSpanCoordinate sigma S q ell) := by
  let L := hilbertConjSpanCoordinateExtension sigma ell
  let coefficient : Fin n → Fin n → ℂ := fun i j ↦
    L (matrixHilbertEquiv n (Matrix.single i j 1))
  let term : Fin n → Fin n → C(S → G, ℂ) := fun i j ↦
    coefficient i j • representedHolonomyEntry sigma S q i j
  have hterm (i j : Fin n) :
      HomogeneousFeatureExpansion (matrixFeature sigma) q.length
        (term i j) :=
    HomogeneousFeatureExpansion.smul (coefficient i j)
      (representedHolonomyEntry_homogeneous sigma S q hq i j)
  let row : Fin n → C(S → G, ℂ) := fun i ↦ ∑ j, term i j
  have hrow (i : Fin n) :
      HomogeneousFeatureExpansion (matrixFeature sigma) q.length (row i) :=
    HomogeneousFeatureExpansion.sum (fun j ↦ term i j) (hterm i)
  let htotal : HomogeneousFeatureExpansion (matrixFeature sigma) q.length
      (∑ i, row i) :=
    HomogeneousFeatureExpansion.sum row hrow
  refine htotal.congr ?_
  ext U
  let M : Matrix (Fin n) (Fin n) ℂ :=
    sigma.ρ (holonomy (extendFromFinset S U) q)
  have hLM : L (matrixHilbertEquiv n M) =
      ∑ i, ∑ j, coefficient i j * M i j := by
    have hM : M = ∑ i, ∑ j, M i j • Matrix.single i j 1 := by
      calc
        M = ∑ i, ∑ j, Matrix.single i j (M i j) :=
          Matrix.matrix_eq_sum_single M
        _ = ∑ i, ∑ j, M i j • Matrix.single i j 1 := by
          simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    have hHilbert : matrixHilbertEquiv n M =
        ∑ i, ∑ j, M i j •
          matrixHilbertEquiv n (Matrix.single i j 1) := by
      calc
        matrixHilbertEquiv n M = matrixHilbertEquiv n
            (∑ i, ∑ j, M i j • Matrix.single i j 1) :=
          congrArg (matrixHilbertEquiv n) hM
        _ = _ := by simp only [map_sum, map_smul]
    rw [hHilbert, map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [map_smul, smul_eq_mul, coefficient]
    ring
  simp only [row, term, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    representedHolonomyEntry_apply, representedHilbertConjSpanCoordinate_apply,
    smul_eq_mul]
  rw [← hLM]
  change L (matrixHilbertEquiv n M) = ell (sigmaInHilbertConjSpan sigma
    (holonomy (extendFromFinset S U) q))
  rw [show matrixHilbertEquiv n M =
      (sigmaInHilbertConjSpan sigma
        (holonomy (extendFromFinset S U) q)).1 by rfl]
  exact hilbertConjSpanCoordinateExtension_apply sigma ell _

/-! ## Multilinear screening coordinates -/

/-- Apply a scalar multilinear form to a family of literal represented
holonomy matrices. -/
def representedConjSpanMultilinear
    {m : ℕ} (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) ℂ) : C(S → G, ℂ) where
  toFun U := F (fun j ↦ sigmaInHilbertConjSpan sigma
    (holonomy (extendFromFinset S U) (q j)))
  continuous_toFun := by
    apply F.cont.comp
    apply continuous_pi
    intro j
    exact (continuous_sigmaInHilbertConjSpan sigma).comp <|
      (continuous_holonomy (q j)).comp (continuous_extendFromFinset S)

@[simp]
theorem representedConjSpanMultilinear_apply
    {m : ℕ} (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) ℂ) (U : S → G) :
    representedConjSpanMultilinear sigma S q F U =
      F (fun j ↦ sigmaInHilbertConjSpan sigma
        (holonomy (extendFromFinset S U) (q j))) :=
  rfl

set_option maxHeartbeats 800000 in
-- The finite basis of the nested Hilbert conjugation-span subtype requires
-- extra elaboration time; the resulting declaration is kernel-checked.
/-- Multilinearity and the finite basis turn the individual exact path
expansions into one exact homogeneous endpoint expansion. -/
noncomputable opaque representedConjSpanMultilinear_homogeneous
    {m : ℕ} (sigma : ContinuousUnitaryRepData G n)
    (S : Finset (PositiveEdge d)) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (hq : ∀ j, (q j).edgeSupport ⊆ S)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) ℂ) :
    HomogeneousFeatureExpansion (matrixFeature sigma)
      (∑ j, (q j).length) (representedConjSpanMultilinear sigma S q F) := by
  let A := HilbertConjSpan sigma
  let b := Module.finBasis ℂ A
  let ell : Fin (Module.finrank ℂ A) → A →L[ℂ] ℂ := fun k ↦
    continuousLinearOfFiniteDimensional (b.coord k)
  let coordinate : Fin m → Fin (Module.finrank ℂ A) → C(S → G, ℂ) :=
    fun j k ↦ representedHilbertConjSpanCoordinate sigma S (q j)
      (ell k)
  have hcoordinate (j : Fin m) (k : Fin (Module.finrank ℂ A)) :
      HomogeneousFeatureExpansion (matrixFeature sigma) (q j).length
        (coordinate j k) :=
    representedHilbertConjSpanCoordinate_homogeneous sigma S (q j) (hq j)
      (ell k)
  let term : (Fin m → Fin (Module.finrank ℂ A)) → C(S → G, ℂ) :=
    fun ks ↦ F (fun j ↦ b (ks j)) • ∏ j, coordinate j (ks j)
  have hterm (ks : Fin m → Fin (Module.finrank ℂ A)) :
      HomogeneousFeatureExpansion (matrixFeature sigma)
        (∑ j, (q j).length) (term ks) :=
    HomogeneousFeatureExpansion.smul (F (fun j ↦ b (ks j))) <|
      HomogeneousFeatureExpansion.finProduct (fun j ↦ (q j).length)
        (fun j ↦ coordinate j (ks j)) (fun j ↦ hcoordinate j (ks j))
  let hsum : HomogeneousFeatureExpansion (matrixFeature sigma)
      (∑ j, (q j).length) (∑ ks, term ks) :=
    HomogeneousFeatureExpansion.sum term hterm
  refine hsum.congr ?_
  ext U
  let v : Fin m → A := fun j ↦ sigmaInHilbertConjSpan sigma
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
        coordinate, representedHilbertConjSpanCoordinate_apply, smul_eq_mul,
        ell, continuousLinearOfFiniteDimensional_apply,
        Module.Basis.coord, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Finsupp.lapply_apply, v]
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
    _ = representedConjSpanMultilinear sigma S q F U := rfl

/-! ## Concrete normalized comb mode -/

/-- Collar restriction of one coordinate of the direct normalized endpoint. -/
def conjSpanCombPhiCollarCoordinate {m : ℕ} (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (x : Site d) (i : Fin p) : C(combEndpointCollar (m := m) hd x → G, ℂ) :=
  collarRestriction (combEndpointCollar (m := m) hd x)
    ((conjSpanPhi hd sigma rho T x).component i).toContinuousMap

/-- Every direct endpoint coordinate has the exact total oriented-occurrence
degree. -/
noncomputable opaque conjSpanCombPhiCollarCoordinate_homogeneous
    {m : ℕ} (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (x : Site d) (i : Fin p) :
    HomogeneousFeatureExpansion (matrixFeature sigma)
      (combEndpointDegree (m := m) hd x)
      (conjSpanCombPhiCollarCoordinate hd sigma rho T x i) := by
  let S := combEndpointCollar (m := m) hd x
  let q := combLoops (m := m) hd x
  let F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) ℂ :=
    (ContinuousLinearMap.proj i).compContinuousMultilinearMap
      (conjSpanScreeningForm sigma rho T)
  have hq (j : Fin m) : (q j).edgeSupport ⊆ S := by
    intro e he
    change e ∈ basedLoopSupport q
    rw [basedLoopSupport, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ j, he⟩
  let hraw := representedConjSpanMultilinear_homogeneous sigma S q hq F
  let hscaled := HomogeneousFeatureExpansion.smul
    (endpointNormalizationScale
      (conjSpanTensorField sigma q (conjSpanScreeningForm sigma rho T)) : ℂ)
      hraw
  refine hscaled.congr ?_
  ext U
  simp only [ContinuousMap.smul_apply, representedConjSpanMultilinear_apply,
    conjSpanCombPhiCollarCoordinate, collarRestriction, ContinuousMap.comp_apply,
    LocalField.component_apply, conjSpanPhi, normalizedEndpoint_apply,
    conjSpanTensorField_apply, F,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
    ContinuousMap.coe_mk]
  dsimp only [S, q]

/-- Some collar coordinate of the direct endpoint is nonzero. -/
theorem exists_conjSpanCombPhiCollarCoordinate_ne_zero
    {m : ℕ} (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) :
    ∃ i : Fin p, conjSpanCombPhiCollarCoordinate hd sigma rho T x i ≠ 0 := by
  obtain ⟨Q, hQ⟩ := conjSpanPhi_not_identically_zero hd sigma rho T hT x
  obtain ⟨i, hi⟩ : ∃ i : Fin p, conjSpanPhi hd sigma rho T x Q i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ (funext h)
  refine ⟨i, ?_⟩
  intro hzero
  let S := combEndpointCollar (m := m) hd x
  let V : S → G := restrictToFinset S Q
  have hvalue : conjSpanCombPhiCollarCoordinate hd sigma rho T x i V =
      conjSpanPhi hd sigma rho T x Q i := by
    exact ((conjSpanPhi hd sigma rho T x).component i).dependsOn_support
      (fun e he ↦ extendFromFinset_restrictToFinset_apply S Q e (by
        simpa [S, combEndpointCollar] using he))
  have hz := DFunLike.congr_fun hzero V
  simp only [ContinuousMap.zero_apply] at hz
  exact hi (hvalue ▸ hz)

/-- The direct endpoint supplies the exact nonzero conjugate mode consumed by
the all-coupling extraction chain.  The coefficient family is the coordinate
form of the conjugated tensor functional; `matrixFeatureExpansion_star`
implements the swap-transpose action explicitly by flipping each doubled
feature letter. -/
noncomputable opaque conjSpanCombEndpointConjugateMode
    {m : ℕ} (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (x : Site d) :
    EndpointConjugateMode (matrixFeature sigma)
      (fun i ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x i)
      (combEndpointDegree (m := m) hd x) := by
  let hex := exists_conjSpanCombPhiCollarCoordinate_ne_zero
    hd sigma rho T hT x
  let i := Classical.choose hex
  have hi : conjSpanCombPhiCollarCoordinate hd sigma rho T x i ≠ 0 :=
    Classical.choose_spec hex
  let hhom := conjSpanCombPhiCollarCoordinate_homogeneous
    hd sigma rho T x i
  let hstar := matrixFeatureExpansion_star sigma
    (combEndpointCollar (m := m) hd x) hhom
  exact EndpointConjugateMode.ofCoordinate (matrixFeature sigma)
    (fun j ↦ conjSpanCombPhiCollarCoordinate hd sigma rho T x j) i
    hstar.coefficient hi (fun U ↦ by simpa using hstar.expansion U)

end

end YangMills.Gluelump.OneLink
