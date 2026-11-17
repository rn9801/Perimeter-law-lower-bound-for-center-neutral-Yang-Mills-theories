/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.HaarProbability
import GluelumpPerimeterLaw.RepresentationTheory.Occurrence
import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Haar averaging of maps between finite-dimensional unitary representations

This file constructs the Reynolds operator on linear maps between the
project's fixed-coordinate continuous unitary representations.  Averaging
`A` by `g ↦ eta(g) A rho(g⁻¹)` produces an intertwiner.  Applying this to a
rank-one map gives the matrix-coefficient orthogonality statement needed by
the gluelump representation-theory layer.
-/

namespace YangMills.Gluelump.RepresentationTheory

open MeasureTheory Representation YangMills.Gauge YangMills.Wilson
open scoped Matrix

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

variable {n m : ℕ}

private theorem continuous_haarAverageIntegrand
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (x : Fin n → ℂ) :
    Continuous (fun g => asRepresentation eta g
      (A (asRepresentation rho g⁻¹ x))) := by
  change Continuous (fun g => (eta.ρ g : Matrix (Fin m) (Fin m) ℂ) *ᵥ
    A ((rho.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x))
  apply Continuous.matrix_mulVec
  · exact continuous_subtype_val.comp eta.continuous_ρ
  · exact A.continuous_of_finiteDimensional.comp
      ((continuous_subtype_val.comp
        (rho.continuous_ρ.comp continuous_inv)).matrix_mulVec continuous_const)

private theorem integrable_haarAverageIntegrand
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (x : Fin n → ℂ) :
    Integrable (fun g => asRepresentation eta g
      (A (asRepresentation rho g⁻¹ x))) (GaugeHaarProbability.haar G) :=
  (continuous_haarAverageIntegrand rho eta A x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Haar average of `A` under the left-right action
`A ↦ eta(g) A rho(g⁻¹)`. -/
def haarAverageLinearMap
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun x := ∫ g, asRepresentation eta g
    (A (asRepresentation rho g⁻¹ x)) ∂GaugeHaarProbability.haar G
  map_add' x y := by
    simp only [map_add]
    rw [integral_add (integrable_haarAverageIntegrand rho eta A x)
      (integrable_haarAverageIntegrand rho eta A y)]
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul c _

/-- The Haar average commutes with the two representation actions. -/
theorem haarAverageLinearMap_isIntertwining
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (h : G) (x : Fin n → ℂ) :
    haarAverageLinearMap rho eta A (asRepresentation rho h x) =
      asRepresentation eta h (haarAverageLinearMap rho eta A x) := by
  change (∫ g, asRepresentation eta g
      (A (asRepresentation rho g⁻¹ (asRepresentation rho h x)))
        ∂GaugeHaarProbability.haar G) = _
  calc
    _ = ∫ g, asRepresentation eta (h * g)
        (A (asRepresentation rho (h * g)⁻¹
          (asRepresentation rho h x))) ∂GaugeHaarProbability.haar G := by
      symm
      exact integral_mul_left_eq_self (μ := GaugeHaarProbability.haar G)
        (fun g : G => asRepresentation eta g
          (A (asRepresentation rho g⁻¹ (asRepresentation rho h x)))) h
    _ = ∫ g, asRepresentation eta h
        (asRepresentation eta g (A (asRepresentation rho g⁻¹ x)))
          ∂GaugeHaarProbability.haar G := by
      congr 1
      funext g
      simp [map_mul, Module.End.mul_apply]
    _ = asRepresentation eta h
        (∫ g, asRepresentation eta g (A (asRepresentation rho g⁻¹ x))
          ∂GaugeHaarProbability.haar G) := by
      exact ((asRepresentation eta h).toContinuousLinearMap.integral_comp_comm
        (integrable_haarAverageIntegrand rho eta A x))
    _ = _ := rfl

/-- The Reynolds average bundled as an intertwining map. -/
def haarAverageIntertwiningMap
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    IntertwiningMap (asRepresentation rho) (asRepresentation eta) :=
  (haarAverageLinearMap rho eta A).intertwiningMap_of_isIntertwiningMap
    _ _ (haarAverageLinearMap_isIntertwining rho eta A)

/-- Haar averaging fixes a map that already intertwines the actions. -/
theorem haarAverageLinearMap_eq_self_of_intertwiner
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (S : IntertwiningMap (asRepresentation rho) (asRepresentation eta)) :
    haarAverageLinearMap rho eta S.toLinearMap = S.toLinearMap := by
  apply LinearMap.ext
  intro x
  change (∫ g, asRepresentation eta g
    (S (asRepresentation rho g⁻¹ x)) ∂GaugeHaarProbability.haar G) = S x
  have hfun : (fun g => asRepresentation eta g
      (S (asRepresentation rho g⁻¹ x))) = fun _g : G => S x := by
    funext g
    rw [← S.isIntertwining]
    simp
  rw [hfun]
  simp

/-- Compact complete reducibility in the orientation needed by endpoint
construction: a nonzero embedding of an irreducible unitary representation
has an equivariant left inverse. -/
theorem exists_intertwiner_leftInverse
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    [IsIrreducible (asRepresentation rho)]
    (S : IntertwiningMap (asRepresentation rho) (asRepresentation eta))
    (hS : S ≠ 0) :
    ∃ T : IntertwiningMap (asRepresentation eta) (asRepresentation rho),
      T.comp S = 1 := by
  have hinj : Function.Injective S :=
    injective_of_irreducible_of_ne_zero S hS
  have hker : LinearMap.ker S.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  let L := S.toLinearMap.leftInverse
  let T := haarAverageIntertwiningMap eta rho L
  refine ⟨T, ?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change haarAverageLinearMap eta rho L (S x) = x
  change (∫ g, asRepresentation rho g
    (L (asRepresentation eta g⁻¹ (S x)))
      ∂GaugeHaarProbability.haar G) = x
  have hfun : (fun g => asRepresentation rho g
      (L (asRepresentation eta g⁻¹ (S x)))) = fun _g : G => x := by
    funext g
    rw [← S.isIntertwining]
    dsimp [L]
    have hleft : S.toLinearMap.leftInverse
        (S ((rho.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x)) =
        (rho.ρ g⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x := by
      exact LinearMap.leftInverse_apply_of_inj hker _
    rw [hleft]
    simp
  rw [hfun]
  simp

/-- Rank-one linear map `x ↦ phi(x) w`. -/
def rankOneLinearMap (phi : Module.Dual ℂ (Fin n → ℂ))
    (w : Fin m → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun x := phi x • w
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp]
theorem rankOneLinearMap_apply (phi : Module.Dual ℂ (Fin n → ℂ))
    (w : Fin m → ℂ) (x : Fin n → ℂ) :
    rankOneLinearMap phi w x = phi x • w := rfl

/-- If there are no intertwiners from `rho` to `eta`, every mixed pair of
their matrix coefficients is orthogonal in Haar `L²`. -/
theorem compact_schur_matrixCoefficient_orthogonal
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G m)
    (hno : ∀ f : IntertwiningMap (asRepresentation rho)
      (asRepresentation eta), f = 0)
    (v : Fin n → ℂ) (phi : Module.Dual ℂ (Fin n → ℂ))
    (w : Fin m → ℂ) (psi : Module.Dual ℂ (Fin m → ℂ)) :
    ∫ g, psi (asRepresentation eta g w) *
      phi (asRepresentation rho g⁻¹ v) ∂GaugeHaarProbability.haar G = 0 := by
  let A := rankOneLinearMap phi w
  let P := haarAverageIntertwiningMap rho eta A
  have hP : P = 0 := hno P
  have hPv : haarAverageLinearMap rho eta A v = 0 := by
    have happ := congrArg
      (fun f : IntertwiningMap (asRepresentation rho) (asRepresentation eta) => f v) hP
    simpa [P, haarAverageIntertwiningMap] using happ
  calc
    _ = ∫ g, psi (asRepresentation eta g
        (A (asRepresentation rho g⁻¹ v))) ∂GaugeHaarProbability.haar G := by
      congr 1
      funext g
      simp [A, rankOneLinearMap, map_smul]
      ring
    _ = psi (∫ g, asRepresentation eta g
        (A (asRepresentation rho g⁻¹ v)) ∂GaugeHaarProbability.haar G) := by
      exact psi.toContinuousLinearMap.integral_comp_comm
        (integrable_haarAverageIntegrand rho eta A v)
    _ = psi (haarAverageLinearMap rho eta A v) := rfl
    _ = 0 := by rw [hPv]; simp

end

end YangMills.Gluelump.RepresentationTheory
