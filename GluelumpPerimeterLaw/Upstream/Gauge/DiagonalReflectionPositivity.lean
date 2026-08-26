/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflection
import YangMills.Gauge.DiagonalReflectionPositivity

/-! Additive measure invariance and Hermitian symmetry for diagonal reflection. -/

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace YangMills.Gauge.DiagonalReflection

noncomputable section

variable {G O P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace WilsonActionDecomposition

variable (D : WilsonActionDecomposition G n O P Q)

section Haar

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]
  [Fintype O] [Fintype P] [Fintype Q]

omit [TopologicalSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] in
/-- Swapping the two strict diagonal half-volume fields preserves reflected
product Haar measure. -/
theorem measurePreserving_reflect :
    MeasurePreserving
      (reflect : ReflectedConfiguration G O P → ReflectedConfiguration G O P)
      reflectedHaar reflectedHaar := by
  have hswap : MeasurePreserving
      (Prod.swap : SideConfiguration G P × SideConfiguration G P →
        SideConfiguration G P × SideConfiguration G P)
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) :=
    Measure.measurePreserving_swap
  simpa only [reflect] using
    MeasurePreserving.prod
      (MeasurePreserving.id (planeHaar (G := G) (O := O))) hswap

omit [CompactSpace G] in
/-- A reflection-invariant diagonal Boltzmann weight makes the full
reflected product-Haar integral invariant under swapping its two sides. -/
theorem integral_boltzmannWeight_comp_reflect (β : ℝ)
    (F : C(ReflectedConfiguration G O P, ℂ)) :
    (∫ U, (D.boltzmannWeight β U : ℂ) * F (reflect U) ∂reflectedHaar) =
      ∫ U, (D.boltzmannWeight β U : ℂ) * F U ∂reflectedHaar := by
  let K : ReflectedConfiguration G O P → ℂ := fun U =>
    (D.boltzmannWeight β U : ℂ) * F U
  have hK : Continuous K := by
    unfold K
    exact (Complex.continuous_ofReal.comp
      (D.continuous_boltzmannWeight β)).mul F.continuous
  rw [show (fun U => (D.boltzmannWeight β U : ℂ) * F (reflect U)) =
      fun U => K (reflect U) by
    funext U
    simp only [K, D.action_reflect, boltzmannWeight]]
  calc
    (∫ U, K (reflect U) ∂reflectedHaar) =
        ∫ U, K U ∂Measure.map reflect reflectedHaar :=
      (MeasureTheory.integral_map continuous_reflect.measurable.aemeasurable
        hK.aestronglyMeasurable).symm
    _ = ∫ U, K U ∂reflectedHaar := by
      rw [(measurePreserving_reflect (G := G) (O := O) (P := P)).map_eq]

/-- Hermitian symmetry of the normalized diagonal reflection pairing. -/
theorem reflectionInnerProduct_conj_symm (β : ℝ)
    (F H : PositiveObservable G O P) :
    conj (D.reflectionInnerProduct β H F) =
      D.reflectionInnerProduct β F H := by
  unfold reflectionInnerProduct
  rw [map_mul, D.gibbsReflectionPairing_conj_symm β F H]
  have hreal : conj ((D.partitionFunction β : ℂ)⁻¹) =
      (D.partitionFunction β : ℂ)⁻¹ := by
    apply Complex.ext <;> simp
  rw [hreal]

end Haar

end WilsonActionDecomposition

end


end YangMills.Gauge.DiagonalReflection
