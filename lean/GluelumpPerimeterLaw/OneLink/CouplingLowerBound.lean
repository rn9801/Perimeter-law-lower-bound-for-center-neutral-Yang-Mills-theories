/-
Copyright (c) 2026 The Gluelump Perimeter Law Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Gluelump Perimeter Law contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteOneLinkLowerBound
import GluelumpPerimeterLaw.Propagation.CouplingRate

/-!
# A coupling-independent coefficient for the one-link estimate

The screening degree and map in this file are fixed before the coupling.
Unfolding the existing all-coupling constant exhibits its exact monomial
and exponential factors, so its logarithmic rate is uniform in `beta`.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint Propagation
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

/-- The nested comb has the same polynomial degree `m(m+3)` used in
the paper's quantitative one-edge estimate. -/
theorem combEndpointDegree_eq (hd : 3 ≤ d) (x : Site d) :
    combEndpointDegree (m := m) hd x = m * (m + 3) := by
  have hsum : ∀ k : ℕ, (∑ j : Fin k, (j.val + 1 + 1 + (j.val + 1) + 1)) =
      k * (k + 3) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, ih]
        ring
  simpa only [combEndpointDegree, combLoops, transverseLoop,
    Path.length_rectangleBoundary] using hsum m

/-- The fixed positive prefactor in the direct one-link estimate. -/
def conjSpanOneLinkPrefactor
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) : ℝ :=
  conjSpanCombScalarMass hd sigma rho T hT x ^ 2 /
    ((combEndpointDegree (m := m) hd x).factorial *
      conjSpanCombExtractionBound hd sigma rho T hT x * (2 * (n : ℝ)) ^
        combEndpointDegree (m := m) hd x)

theorem conjSpanOneLinkPrefactor_pos
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanOneLinkPrefactor hd sigma rho T hT x := by
  have hA := conjSpanCombScalarMass_pos hd sigma rho T hT x
  have hH := conjSpanCombExtractionBound_pos hd sigma rho T hT x
  have hn : (0 : ℝ) < n := by exact_mod_cast sigma.dimension_pos
  have hfactorial : (0 : ℝ) < (combEndpointDegree (m := m) hd x).factorial := by
    exact_mod_cast Nat.factorial_pos (combEndpointDegree (m := m) hd x)
  unfold conjSpanOneLinkPrefactor
  positivity

/-- The fixed decay coefficient after both finite-energy comparisons and
the selected-kernel normalization. -/
def conjSpanOneLinkDecay (hd : 3 ≤ d) (x : Site d) : ℝ :=
  20 * d * (combEndpointCollar (m := m) hd x).card

theorem conjSpanOneLinkLowerConstant_eq_monomial_exp
    (beta : ℝ) (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT x =
      conjSpanOneLinkPrefactor hd sigma rho T hT x *
        beta ^ combEndpointDegree (m := m) hd x *
          Real.exp (-conjSpanOneLinkDecay (m := m) hd x * beta) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast sigma.dimension_pos.ne'
  have henergy :
      collarFiniteEnergyFactor beta sigma.wilsonPotential
          (combEndpointCollar (m := m) hd x) ^ 2 /
        linkCombLocalKernelBound (m := m) beta hd x n =
          Real.exp (-conjSpanOneLinkDecay (m := m) hd x * beta) := by
    unfold collarFiniteEnergyFactor linkCombLocalKernelBound conjSpanOneLinkDecay
    change Real.exp (-beta * (2 * 1 *
        (4 * d * (combEndpointCollar (m := m) hd x).card))) ^ 2 /
      Real.exp ((beta / (2 * n)) *
        (2 * n * (4 * d * (combEndpointCollar (m := m) hd x).card))) = _
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    field_simp [hn]
    <;> ring
  calc
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT x =
        conjSpanOneLinkPrefactor hd sigma rho T hT x *
          beta ^ combEndpointDegree (m := m) hd x *
            (collarFiniteEnergyFactor beta sigma.wilsonPotential
                (combEndpointCollar (m := m) hd x) ^ 2 /
              linkCombLocalKernelBound (m := m) beta hd x n) := by
      unfold conjSpanOneLinkLowerConstant allCouplingLowerConstant
        conjSpanOneLinkPrefactor
      simp only [div_pow, div_eq_mul_inv, mul_inv_rev]
      ring_nf
      norm_num
    _ = _ := by rw [henergy]

/-- One fixed rate coefficient for the chosen screening field. -/
def conjSpanOneLinkCouplingConstant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) : ℝ :=
  monomialCouplingConstant (conjSpanOneLinkPrefactor hd sigma rho T hT x)
    (conjSpanOneLinkDecay (m := m) hd x) (combEndpointDegree (m := m) hd x)

theorem conjSpanOneLinkCouplingConstant_pos
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanOneLinkCouplingConstant hd sigma rho T hT x := by
  apply monomialCouplingConstant_pos
  unfold conjSpanOneLinkDecay
  positivity

theorem exp_neg_conjSpanOneLinkCouplingConstant_le_lowerConstant
    {beta : ℝ} (hbeta : 0 < beta)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    Real.exp (-conjSpanOneLinkCouplingConstant hd sigma rho T hT x *
        couplingWeight beta) ≤
      conjSpanOneLinkLowerConstant beta hd sigma rho T hT x := by
  rw [conjSpanOneLinkLowerConstant_eq_monomial_exp]
  apply exp_neg_couplingWeight_le_monomial
    (conjSpanOneLinkPrefactor_pos hd sigma rho T hT x)
  · unfold conjSpanOneLinkDecay
    positivity
  · exact hbeta

/-- The fixed coefficient in the paper's unnormalized-character coupling.
The two ordered plaquette labels are already present in the finite action,
so the conversion is `beta_Lean = n * beta_paper`. -/
def conjSpanOneLinkPaperCouplingConstant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) : ℝ :=
  monomialCouplingConstant
    (conjSpanOneLinkPrefactor hd sigma rho T hT x *
      (n : ℝ) ^ combEndpointDegree (m := m) hd x)
    (conjSpanOneLinkDecay (m := m) hd x * n)
    (combEndpointDegree (m := m) hd x)

theorem conjSpanOneLinkPaperCouplingConstant_pos
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    0 < conjSpanOneLinkPaperCouplingConstant hd sigma rho T hT x := by
  apply monomialCouplingConstant_pos
  unfold conjSpanOneLinkDecay
  positivity

theorem exp_neg_conjSpanOneLinkPaperCouplingConstant_le_lowerConstant
    {beta : ℝ} (hbeta : 0 < beta)
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0) (x : Site d) :
    Real.exp (-conjSpanOneLinkPaperCouplingConstant hd sigma rho T hT x *
        couplingWeight beta) ≤
      conjSpanOneLinkLowerConstant ((n : ℝ) * beta) hd sigma rho T hT x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast sigma.dimension_pos
  rw [conjSpanOneLinkLowerConstant_eq_monomial_exp]
  have hA : 0 < conjSpanOneLinkPrefactor hd sigma rho T hT x *
      (n : ℝ) ^ combEndpointDegree (m := m) hd x :=
    mul_pos (conjSpanOneLinkPrefactor_pos hd sigma rho T hT x)
      (pow_pos hn (combEndpointDegree (m := m) hd x))
  have h := exp_neg_couplingWeight_le_monomial hA
    (show 0 ≤ conjSpanOneLinkDecay (m := m) hd x * (n : ℝ) by
      unfold conjSpanOneLinkDecay
      positivity) hbeta (combEndpointDegree (m := m) hd x)
  simpa only [conjSpanOneLinkPaperCouplingConstant, mul_pow, neg_mul, mul_assoc] using h

end

end YangMills.Gluelump.OneLink
