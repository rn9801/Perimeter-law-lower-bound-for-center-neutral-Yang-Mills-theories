/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.FaithfulMatrixCoefficients
import GluelumpPerimeterLaw.RepresentationTheory.HaarAverage
import Mathlib.LinearAlgebra.TensorPower.Pairing

/-!
# Tensor generation from faithful unitary matrix coefficients

This file turns the Stone--Weierstrass detection theorem for finite words into
an actual equivariant map from a tensor power.  The source is assumed
self-dual, so conjugated matrix entries can be written as ordinary source
coefficients.  Averaging a rank-one map then gives the required orientation
directly; no irreducible decomposition or Peter--Weyl theorem is used.
-/

namespace YangMills.Gluelump.RepresentationTheory

open MeasureTheory Representation YangMills.Gauge YangMills.Wilson
open scoped Matrix TensorProduct BigOperators

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

variable {n p : ℕ}

/-- Evaluation at one coordinate, as an algebraic dual vector. -/
def coordinateDual (i : Fin n) : Module.Dual ℂ (Fin n → ℂ) where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A standard coordinate vector. -/
def coordinateVector (j : Fin n) : Fin n → ℂ := Pi.single j 1

@[simp]
theorem coordinateDual_coordinateVector (i j : Fin n) :
    coordinateDual i (coordinateVector j) = if i = j then 1 else 0 := by
  simp [coordinateDual, coordinateVector, Pi.single_apply]

/-- Source vector attached to an oriented matrix entry.  A conjugated entry
is transported from the algebraic dual through the chosen self-duality. -/
def matrixFeatureVector (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    (a : MatrixFeatureLetter Unit n) : Fin n → ℂ :=
  if a.2.1 then self.symm (coordinateDual a.2.2.2)
  else coordinateVector a.2.2.2

/-- Dual vector attached to an oriented matrix entry. -/
def matrixFeatureDual (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    (a : MatrixFeatureLetter Unit n) : Module.Dual ℂ (Fin n → ℂ) :=
  if a.2.1 then
    (Module.Dual.eval ℂ (Fin n → ℂ) (coordinateVector a.2.2.1)).comp
      self.toLinearMap
  else coordinateDual a.2.2.1

/-- Each oriented matrix entry is an ordinary coefficient of a self-dual
source representation. -/
theorem matrixFeature_eq_dual_apply_rep
    (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    (a : MatrixFeatureLetter Unit n) (g : G) :
    matrixFeature rho a (fun _ => g) =
      matrixFeatureDual rho self a
        (asRepresentation rho g (matrixFeatureVector rho self a)) := by
  rcases a with ⟨u, b, i, j⟩
  fin_cases u
  cases b
  · simp [matrixFeature, matrixFeatureDual, matrixFeatureVector,
      coordinateDual, coordinateVector, Matrix.mulVec_single_one]
  · change star ((rho.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) = _
    have hintertwine := IntertwiningMap.isIntertwining
      (asRepresentation rho) (asRepresentation rho).dual
      self.toIntertwiningMap g (self.symm (coordinateDual j))
    have hdual : (asRepresentation rho).dual g (coordinateDual j) =
        self (asRepresentation rho g (self.symm (coordinateDual j))) := by
      simpa using hintertwine.symm
    simp only [matrixFeatureDual, matrixFeatureVector, if_true,
      LinearMap.comp_apply, Module.Dual.eval_apply]
    calc
      star ((rho.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) =
          ((asRepresentation rho).dual g (coordinateDual j))
            (coordinateVector i) := by
        change star ((rho.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) =
          coordinateDual j
            (asRepresentation rho g⁻¹ (coordinateVector i))
        simp [coordinateDual, coordinateVector, Matrix.mulVec, dotProduct,
          Pi.single_apply, map_inv, Matrix.UnitaryGroup.inv_val,
          Matrix.star_eq_conjTranspose]
      _ = self (asRepresentation rho g (self.symm (coordinateDual j)))
            (coordinateVector i) := congrArg
        (fun phi : Module.Dual ℂ (Fin n → ℂ) => phi (coordinateVector i)) hdual

/-- Product functional on a homogeneous tensor power. -/
def tensorWordDual (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n) :
    Module.Dual ℂ (⨂[ℂ]^m (Fin n → ℂ)) :=
  TensorPower.multilinearMapToDual ℂ (Fin n → ℂ) m
    (fun r => matrixFeatureDual rho self (w r))

/-- Pure tensor of the vectors attached to a matrix word. -/
def tensorWordVector (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n) :
    ⨂[ℂ]^m (Fin n → ℂ) :=
  PiTensorProduct.tprod ℂ (fun r => matrixFeatureVector rho self (w r))

@[simp]
theorem tensorWord_coefficient
    (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n) (g : G) :
    tensorWordDual rho self w
        (tensorPower (asRepresentation rho) m g
          (tensorWordVector rho self w)) =
      matrixFeatureFinMonomial rho w (fun _ => g) := by
  simp only [tensorWordDual, tensorWordVector, tensorPower_tprod,
    TensorPower.multilinearMapToDual_apply_tprod,
    matrixFeatureFinMonomial, ContinuousMap.prod_apply]
  apply Finset.prod_congr rfl
  intro r _
  exact (matrixFeature_eq_dual_apply_rep rho self (w r) g).symm

private theorem continuous_matrixCoefficient
    (rho : ContinuousUnitaryRepData G n)
    (phi : Module.Dual ℂ (Fin n → ℂ)) (v : Fin n → ℂ) :
    Continuous (fun g => phi (asRepresentation rho g v)) := by
  exact phi.continuous_of_finiteDimensional.comp
    ((continuous_subtype_val.comp rho.continuous_ρ).matrix_mulVec continuous_const)

/-- A product functional evaluated along any tensor-power orbit is
continuous.  The proof uses that algebraic tensor powers are spanned by pure
tensors; no topology on the algebraic tensor product is needed. -/
private theorem continuous_tensorWordDual_orbit
    (rho : ContinuousUnitaryRepData G n)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (x : ⨂[ℂ]^m (Fin n → ℂ)) :
    Continuous (fun g => tensorWordDual rho self w
      (tensorPower (asRepresentation rho) m g x)) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff c v =>
      simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
        tensorPower_tprod, tensorWordDual,
        TensorPower.multilinearMapToDual_apply_tprod]
      exact continuous_const.mul (continuous_finset_prod _ fun r _ =>
        continuous_matrixCoefficient rho (matrixFeatureDual rho self (w r)) (v r))
  | add x y hx hy =>
      simpa only [map_add] using hx.add hy

private theorem continuous_tensorWordAverageIntegrand
    (rho : ContinuousUnitaryRepData G n)
    (lambda : ContinuousUnitaryRepData G p)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (v : Fin p → ℂ) (x : ⨂[ℂ]^m (Fin n → ℂ)) :
    Continuous (fun g =>
      tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹ x) •
        asRepresentation lambda g v) := by
  apply Continuous.smul
  · exact (continuous_tensorWordDual_orbit rho self w x).comp continuous_inv
  · exact (continuous_subtype_val.comp lambda.continuous_ρ).matrix_mulVec
      continuous_const

private theorem integrable_tensorWordAverageIntegrand
    (rho : ContinuousUnitaryRepData G n)
    (lambda : ContinuousUnitaryRepData G p)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (v : Fin p → ℂ) (x : ⨂[ℂ]^m (Fin n → ℂ)) :
    Integrable (fun g =>
      tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹ x) •
        asRepresentation lambda g v) (GaugeHaarProbability.haar G) :=
  (continuous_tensorWordAverageIntegrand rho lambda self w v x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Haar average of the rank-one map associated to a tensor word. -/
def tensorWordHaarAverage
    (rho : ContinuousUnitaryRepData G n)
    (lambda : ContinuousUnitaryRepData G p)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (v : Fin p → ℂ) :
    (⨂[ℂ]^m (Fin n → ℂ)) →ₗ[ℂ] (Fin p → ℂ) where
  toFun x := ∫ g, tensorWordDual rho self w
      (tensorPower (asRepresentation rho) m g⁻¹ x) •
        asRepresentation lambda g v ∂GaugeHaarProbability.haar G
  map_add' x y := by
    simp only [map_add, add_smul]
    rw [integral_add (integrable_tensorWordAverageIntegrand rho lambda self w v x)
      (integrable_tensorWordAverageIntegrand rho lambda self w v y)]
  map_smul' c x := by
    simp only [map_smul, smul_assoc, RingHom.id_apply]
    rw [← integral_smul]

/-- The rank-one Haar average intertwines the tensor-power source and the
target matrix representation. -/
theorem tensorWordHaarAverage_isIntertwining
    (rho : ContinuousUnitaryRepData G n)
    (lambda : ContinuousUnitaryRepData G p)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (v : Fin p → ℂ) (h : G) (x : ⨂[ℂ]^m (Fin n → ℂ)) :
    tensorWordHaarAverage rho lambda self w v
        (tensorPower (asRepresentation rho) m h x) =
      asRepresentation lambda h (tensorWordHaarAverage rho lambda self w v x) := by
  change (∫ g, tensorWordDual rho self w
      (tensorPower (asRepresentation rho) m g⁻¹
        (tensorPower (asRepresentation rho) m h x)) •
        asRepresentation lambda g v ∂GaugeHaarProbability.haar G) = _
  calc
    _ = ∫ g, tensorWordDual rho self w
        (tensorPower (asRepresentation rho) m (h * g)⁻¹
          (tensorPower (asRepresentation rho) m h x)) •
          asRepresentation lambda (h * g) v
          ∂GaugeHaarProbability.haar G := by
      symm
      exact integral_mul_left_eq_self
        (fun g : G => tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹
            (tensorPower (asRepresentation rho) m h x)) •
            asRepresentation lambda g v) h
    _ = ∫ g, asRepresentation lambda h
        (tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹ x) •
            asRepresentation lambda g v) ∂GaugeHaarProbability.haar G := by
      congr 1
      funext g
      have htensor : tensorPower (asRepresentation rho) m (h * g)⁻¹
          (tensorPower (asRepresentation rho) m h x) =
          tensorPower (asRepresentation rho) m g⁻¹ x := by
        rw [← Module.End.mul_apply, ← map_mul]
        congr 1
        group
      rw [htensor]
      simp [map_mul, Module.End.mul_apply]
    _ = asRepresentation lambda h
        (∫ g, tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹ x) •
            asRepresentation lambda g v ∂GaugeHaarProbability.haar G) := by
      exact ((asRepresentation lambda h).toContinuousLinearMap.integral_comp_comm
        (integrable_tensorWordAverageIntegrand rho lambda self w v x))
    _ = _ := rfl

/-- The Haar average bundled as an intertwining map. -/
def tensorWordHaarIntertwiner
    (rho : ContinuousUnitaryRepData G n)
    (lambda : ContinuousUnitaryRepData G p)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    {m : ℕ} (w : Fin m → MatrixFeatureLetter Unit n)
    (v : Fin p → ℂ) :
    IntertwiningMap (tensorPower (asRepresentation rho) m)
      (asRepresentation lambda) :=
  (tensorWordHaarAverage rho lambda self w v).intertwiningMap_of_isIntertwiningMap
    _ _ (tensorWordHaarAverage_isIntertwining rho lambda self w v)

/-- A faithful self-dual continuous unitary matrix representation generates
every positive-dimensional continuous unitary matrix representation in the
operational orientation `tensorPower → target`.

Stone--Weierstrass supplies a word with a nonzero mixed Haar integral;
`tensorWord_coefficient` identifies that word with a tensor coefficient, and
the explicitly averaged rank-one map has that integral as one matrix entry. -/
theorem faithful_selfDual_tensorPower_mapsTo_rep
    (rho : ContinuousUnitaryRepData G n)
    (hrho : Function.Injective rho.ρ)
    (self : (asRepresentation rho).Equiv (asRepresentation rho).dual)
    (lambda : ContinuousUnitaryRepData G p) :
    ∃ m : ℕ, ∃ T : IntertwiningMap (tensorPower (asRepresentation rho) m)
        (asRepresentation lambda), T ≠ 0 := by
  let i : Fin p := ⟨0, lambda.dimension_pos⟩
  let f : C(Unit → G, ℂ) := {
    toFun := fun U => coordinateDual i
      (asRepresentation lambda (U ())⁻¹ (coordinateVector i))
    continuous_toFun := (continuous_matrixCoefficient lambda
      (coordinateDual i) (coordinateVector i)).comp
        (continuous_inv.comp (continuous_apply ())) }
  have hf : f ≠ 0 := by
    intro hfzero
    have happ := congrArg (fun q : C(Unit → G, ℂ) => q (fun _ => 1)) hfzero
    simpa [f, i, coordinateDual, coordinateVector] using happ
  obtain ⟨m, w, hw⟩ :=
    exists_matrixFeatureFinMonomial_integral_ne_zero rho hrho f hf
  let T := tensorWordHaarIntertwiner rho lambda self w (coordinateVector i)
  refine ⟨m, T, ?_⟩
  intro hT
  have hentry : coordinateDual i
      (T (tensorWordVector rho self w)) = 0 := by
    have happ := congrArg
      (fun q : IntertwiningMap (tensorPower (asRepresentation rho) m)
        (asRepresentation lambda) =>
          coordinateDual i (q (tensorWordVector rho self w))) hT
    simpa using happ
  have hintegral : coordinateDual i
      (T (tensorWordVector rho self w)) =
        ∫ g, f (fun _ => g) * matrixFeatureFinMonomial rho w (fun _ => g)
          ∂GaugeHaarProbability.haar G := by
    change coordinateDual i
      (∫ g, tensorWordDual rho self w
        (tensorPower (asRepresentation rho) m g⁻¹
          (tensorWordVector rho self w)) •
          asRepresentation lambda g (coordinateVector i)
          ∂GaugeHaarProbability.haar G) = _
    have hcomm :
        (∫ g, coordinateDual i
          (tensorWordDual rho self w
            (tensorPower (asRepresentation rho) m g⁻¹
              (tensorWordVector rho self w)) •
            asRepresentation lambda g (coordinateVector i))
            ∂GaugeHaarProbability.haar G) =
          coordinateDual i
            (∫ g, tensorWordDual rho self w
              (tensorPower (asRepresentation rho) m g⁻¹
                (tensorWordVector rho self w)) •
              asRepresentation lambda g (coordinateVector i)
              ∂GaugeHaarProbability.haar G) := by
      simpa using (coordinateDual i).toContinuousLinearMap.integral_comp_comm
        (integrable_tensorWordAverageIntegrand rho lambda self w
          (coordinateVector i) (tensorWordVector rho self w))
    rw [← hcomm]
    rw [← integral_inv_eq_self
      (fun g : G => coordinateDual i
        (tensorWordDual rho self w
          (tensorPower (asRepresentation rho) m g⁻¹
            (tensorWordVector rho self w)) •
          asRepresentation lambda g (coordinateVector i)))
      (GaugeHaarProbability.haar G)]
    apply integral_congr_ae
    filter_upwards with g
    simp only [inv_inv, map_smul, smul_eq_mul]
    rw [tensorWord_coefficient]
    change matrixFeatureFinMonomial rho w (fun _ => g) *
        coordinateDual i
          (asRepresentation lambda g⁻¹ (coordinateVector i)) =
      coordinateDual i
          (asRepresentation lambda g⁻¹ (coordinateVector i)) *
        matrixFeatureFinMonomial rho w (fun _ => g)
    exact mul_comm _ _
  have hproduct :
      (∫ U, f U * matrixFeatureFinMonomial rho w U
          ∂ProductHaar.measure G Unit) =
        ∫ g, f (fun _ => g) * matrixFeatureFinMonomial rho w (fun _ => g)
          ∂GaugeHaarProbability.haar G := by
    simpa [ProductHaar.measure] using
      (measurePreserving_piUnique
        (fun _ : Unit => GaugeHaarProbability.haar G)).integral_comp'
          (fun g => f (fun _ => g) *
            matrixFeatureFinMonomial rho w (fun _ => g))
  apply hw
  rw [hproduct, ← hintegral]
  exact hentry

end

end YangMills.Gluelump.RepresentationTheory
