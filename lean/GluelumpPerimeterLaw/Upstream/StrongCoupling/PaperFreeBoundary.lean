/-
Copyright (c) 2026 The Gluelump Perimeter Law Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Gluelump Perimeter Law contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryInfiniteVolume

/-!
# The paper's coupling convention

The ordinary box action uses both ordered plaquette labels. Its Wilson
potential is normalized by `dim sigma`, so the paper coupling `beta` is
exactly the internal coupling `(dim sigma) * beta`.
-/

namespace YangMills.StrongCoupling
open MeasureTheory Gauge Lattice.Cubic Wilson
noncomputable section
variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The exact finite law in the paper, including its coupling normalization. -/
abbrev paperFreeBoundaryGibbsSequence
    (sigma : ContinuousUnitaryRepData G n) (beta : ℝ) (tau : Fin d) (radius : ℕ) :=
  freeBoundaryGibbsSequence (d := d) sigma.wilsonPotential ((n : ℝ) * beta) tau radius

/-- The normalized-potential Boltzmann exponent equals the paper's real
character sum over all oriented plaquettes, with no extra factor of two. -/
theorem paperFreeBoundary_exponent_eq_character_sum
    (sigma : ContinuousUnitaryRepData G n) (beta : ℝ) (tau : Fin d) (radius : ℕ)
    (U : DynamicConfiguration (freeBoundarySpecification G d radius tau)) :
    ((n : ℝ) * beta) * FiniteVolume.action
        (freeBoundarySpecification G d radius tau) sigma.wilsonPotential U =
      beta * ∑ p ∈ (freeBoundarySpecification G d radius tau).activePlaquettes,
        (sigma.character (FiniteVolume.plaquetteHolonomy
          (freeBoundarySpecification G d radius tau) U p)).re := by
  classical
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt sigma.dimension_pos)
  have hscale (g : G) : (n : ℝ) * sigma.wilsonPotential g = (sigma.character g).re := by
    have h : (n : ℂ) * sigma.normalizedCharacter g = sigma.character g := by
      simp [ContinuousUnitaryRepData.normalizedCharacter, hn, ← mul_assoc]
    simpa only [ContinuousUnitaryRepData.wilsonPotential_apply,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      using congrArg Complex.re h
  unfold FiniteVolume.action
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show (n : ℝ) * beta = beta * (n : ℝ) by ring, mul_assoc, hscale]

/-- Assumption 1 of the paper, with ordinary internal-edge finite laws. -/
abbrev IsTranslationInvariantPaperFreeBoundaryLimit
    (sigma : ContinuousUnitaryRepData G n) (beta : ℝ)
    (mu : ProbabilityMeasure (Configuration d G)) : Prop :=
  IsTranslationInvariantFreeBoundaryLimit sigma.wilsonPotential ((n : ℝ) * beta) mu

end
end YangMills.StrongCoupling
