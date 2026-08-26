/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.FiniteEnergy
import YangMills.StrongCoupling.Counting
import YangMills.Gauge.LinkReflectionBridge

/-!
# Volume-independent collar incidence bounds

Changing a fixed finite set of stored edge variables can alter only
plaquettes incident to those edges.  This file packages the existing cubic
lattice incidence list into the exact finite-set estimate required by the
all-coupling finite-energy comparison.  The bound `4 * d` reflects the
repository's ordered plaquette convention; its value is immaterial for
volume uniformity.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic StrongCoupling

noncomputable section

local instance {d : ℕ} : DecidableEq (Plaquette d) := Classical.decEq _

/-- Plaquettes in `P` whose stored boundary meets the edge collar `E`. -/
def plaquettesMeetingEdges {d : ℕ} (P : Finset (Plaquette d))
    (E : Finset (PositiveEdge d)) : Finset (Plaquette d) :=
  P.filter fun p ↦ ¬Disjoint p.boundary.edgeSupport E

@[simp]
theorem mem_plaquettesMeetingEdges {d : ℕ} (P : Finset (Plaquette d))
    (E : Finset (PositiveEdge d)) (p : Plaquette d) :
    p ∈ plaquettesMeetingEdges P E ↔
      p ∈ P ∧ ¬Disjoint p.boundary.edgeSupport E := by
  simp [plaquettesMeetingEdges]

/-- The number of plaquettes affected by a collar is bounded independently
of the ambient plaquette set. -/
theorem card_plaquettesMeetingEdges_le {d : ℕ}
    (P : Finset (Plaquette d)) (E : Finset (PositiveEdge d)) :
    (plaquettesMeetingEdges P E).card ≤ 4 * d * E.card := by
  let candidates : Finset (Plaquette d) := E.biUnion incidentPlaquettes
  have hsubset : plaquettesMeetingEdges P E ⊆ candidates := by
    intro p hp
    have hmeet := (mem_plaquettesMeetingEdges P E p).mp hp |>.2
    rw [Finset.not_disjoint_iff] at hmeet
    obtain ⟨e, hep, heE⟩ := hmeet
    exact Finset.mem_biUnion.mpr
      ⟨e, heE, mem_incidentPlaquettes_of_mem_boundary e p hep⟩
  calc
    (plaquettesMeetingEdges P E).card ≤ candidates.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ e ∈ E, (incidentPlaquettes e).card := by
      simpa [candidates] using
        (Finset.card_biUnion_le (s := E) (t := incidentPlaquettes))
    _ ≤ ∑ _e ∈ E, 4 * d := by
      apply Finset.sum_le_sum
      intro e _he
      exact card_incidentPlaquettes_le e
    _ = 4 * d * E.card := by simp [Nat.mul_comm]

/-- A plaquette outside the affected set has identical holonomy when the two
configurations agree away from the collar. -/
theorem plaquetteHolonomy_eq_of_not_mem_meeting
    {d : ℕ} {G : Type*} [Group G]
    (P : Finset (Plaquette d)) (E : Finset (PositiveEdge d))
    (Q R : Configuration d G)
    (hQR : ∀ e, e ∉ E → Q e = R e)
    (p : Plaquette d) (hp : p ∈ P)
    (hnot : p ∉ plaquettesMeetingEdges P E) :
    holonomy Q p.boundary = holonomy R p.boundary := by
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  apply hQR e
  intro heE
  apply hnot
  rw [mem_plaquettesMeetingEdges]
  exact ⟨hp, Finset.not_disjoint_iff.mpr ⟨e, he, heE⟩⟩

/-- The action difference caused by changing collar variables is controlled
by the number of affected plaquettes and the uniform potential bound. -/
theorem abs_plaquetteAction_sub_le
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (Phi : RealPlaquettePotential G) (P : Finset (Plaquette d))
    (E : Finset (PositiveEdge d)) (Q R : Configuration d G)
    (hQR : ∀ e, e ∉ E → Q e = R e) :
    |∑ p ∈ P, Phi (holonomy Q p.boundary) -
        ∑ p ∈ P, Phi (holonomy R p.boundary)| ≤
      2 * Phi.bound * (plaquettesMeetingEdges P E).card := by
  let delta : Plaquette d → ℝ := fun p ↦
    Phi (holonomy Q p.boundary) - Phi (holonomy R p.boundary)
  have hsum :
      (∑ p ∈ P, Phi (holonomy Q p.boundary)) -
          ∑ p ∈ P, Phi (holonomy R p.boundary) =
        ∑ p ∈ plaquettesMeetingEdges P E, delta p := by
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset
    · intro p hp
      exact (mem_plaquettesMeetingEdges P E p).mp hp |>.1
    · intro p hpP hpnot
      change Phi (holonomy Q p.boundary) - Phi (holonomy R p.boundary) = 0
      rw [plaquetteHolonomy_eq_of_not_mem_meeting P E Q R hQR p hpP hpnot,
        sub_self]
  rw [hsum]
  calc
    |∑ p ∈ plaquettesMeetingEdges P E, delta p| ≤
        ∑ p ∈ plaquettesMeetingEdges P E, |delta p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ plaquettesMeetingEdges P E, (2 * Phi.bound) := by
      apply Finset.sum_le_sum
      intro p _hp
      unfold delta
      calc
        |Phi (holonomy Q p.boundary) - Phi (holonomy R p.boundary)| ≤
            |Phi (holonomy Q p.boundary)| +
              |Phi (holonomy R p.boundary)| := abs_sub _ _
        _ ≤ Phi.bound + Phi.bound := by
          gcongr <;> simpa [Real.norm_eq_abs] using Phi.norm_le_bound _
        _ = 2 * Phi.bound := by ring
    _ = 2 * Phi.bound * (plaquettesMeetingEdges P E).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Fully volume-independent action comparison obtained by combining the
local estimate with the cubic incidence count. -/
theorem abs_plaquetteAction_sub_le_uniform
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (Phi : RealPlaquettePotential G) (P : Finset (Plaquette d))
    (E : Finset (PositiveEdge d)) (Q R : Configuration d G)
    (hQR : ∀ e, e ∉ E → Q e = R e) :
    |∑ p ∈ P, Phi (holonomy Q p.boundary) -
        ∑ p ∈ P, Phi (holonomy R p.boundary)| ≤
      2 * Phi.bound * (4 * d * E.card) := by
  have hcard : ((plaquettesMeetingEdges P E).card : ℝ) ≤
      (4 : ℝ) * d * E.card := by
    exact_mod_cast card_plaquettesMeetingEdges_le P E
  exact (abs_plaquetteAction_sub_le Phi P E Q R hQR).trans <|
    mul_le_mul_of_nonneg_left hcard
      (mul_nonneg (by norm_num) Phi.bound_nonneg)

/-- The explicit fixed-collar finite-energy factor. -/
def collarFiniteEnergyFactor {d : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] (beta : ℝ) (Phi : RealPlaquettePotential G)
    (E : Finset (PositiveEdge d)) : ℝ :=
  Real.exp (-beta * (2 * Phi.bound * (4 * d * E.card)))

theorem collarFiniteEnergyFactor_pos
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (beta : ℝ) (Phi : RealPlaquettePotential G)
    (E : Finset (PositiveEdge d)) :
    0 < collarFiniteEnergyFactor beta Phi E := by
  exact Real.exp_pos _

/-- Changing the collar variables changes a Boltzmann weight by at most the
fixed finite-energy factor, uniformly in the ambient plaquette set. -/
theorem collarFiniteEnergyFactor_mul_exp_action_le
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (Phi : RealPlaquettePotential G) (P : Finset (Plaquette d))
    (E : Finset (PositiveEdge d)) (Q R : Configuration d G)
    (hQR : ∀ e, e ∉ E → Q e = R e) :
    collarFiniteEnergyFactor beta Phi E *
        Real.exp (beta * ∑ p ∈ P, Phi (holonomy R p.boundary)) ≤
      Real.exp (beta * ∑ p ∈ P, Phi (holonomy Q p.boundary)) := by
  let a := ∑ p ∈ P, Phi (holonomy Q p.boundary)
  let b := ∑ p ∈ P, Phi (holonomy R p.boundary)
  let C : ℝ := 2 * Phi.bound * (4 * d * E.card)
  have habs : |a - b| ≤ C := by
    exact abs_plaquetteAction_sub_le_uniform Phi P E Q R hQR
  have hlower : -C ≤ a - b := neg_le_of_abs_le habs
  rw [collarFiniteEnergyFactor, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -beta * C + beta * b ≤ beta * a
  nlinarith [mul_le_mul_of_nonneg_left hlower hbeta]

/-! ## Concrete link-positive half-box comparison -/

/-- The one-sided evaluation map is coordinate-local: if two positive-side
fields agree away from a physical collar, their evaluated full
configurations agree away from that collar as well.  Crossing and negative
labels are fixed to the identity, while a positive label reads exactly its
own side coordinate. -/
theorem linkEvaluateSide_eq_of_not_mem
    {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (E : Finset (PositiveEdge d))
    (U V : LinkReflection.SideConfiguration G
      (Lambda.linkPositiveEdges tau k))
    (hUV : ∀ p, p.1 ∉ E → U p = V p)
    (e : PositiveEdge d) (he : e ∉ E) :
    Lambda.linkEvaluateSide tau k hLambda U e =
      Lambda.linkEvaluateSide tau k hLambda V e := by
  change Lambda.evaluate
      (Lambda.linkAssemble tau k hLambda (1, (1, U))) e =
    Lambda.evaluate
      (Lambda.linkAssemble tau k hLambda (1, (1, V))) e
  by_cases hedyn : e ∈ Lambda.dynamicEdges
  · rw [Lambda.evaluate_of_mem _ e hedyn,
      Lambda.evaluate_of_mem _ e hedyn]
    let edyn : Lambda.dynamicEdges := ⟨e, hedyn⟩
    change Lambda.linkAssemble tau k hLambda (1, (1, U)) edyn =
      Lambda.linkAssemble tau k hLambda (1, (1, V)) edyn
    generalize hlabel : Lambda.linkEdgeLabelEquiv tau k hLambda edyn = label
    rcases label with c | p
    · simp only [FiniteSpecification.linkAssemble, ContinuousMap.coe_mk,
        hlabel]
    · rcases p with p | p
      · simp only [FiniteSpecification.linkAssemble, ContinuousMap.coe_mk,
          hlabel]
      · have heval : e = p.1 := by
          have hsub : edyn =
              (Lambda.linkEdgeLabelEquiv tau k hLambda).symm
                (Sum.inr (Sum.inr p)) := by
            apply (Lambda.linkEdgeLabelEquiv tau k hLambda).injective
            rw [hlabel,
              (Lambda.linkEdgeLabelEquiv tau k hLambda).apply_symm_apply]
          exact congrArg Subtype.val hsub
        simp only [FiniteSpecification.linkAssemble, ContinuousMap.coe_mk,
          hlabel]
        exact hUV p (heval ▸ he)
  · rw [Lambda.evaluate_of_not_mem _ e hedyn,
      Lambda.evaluate_of_not_mem _ e hedyn]

/-- The abstract collar incidence estimate applied to the actual positive
half-box Wilson action.  Its constant depends only on the fixed physical
collar `E`, never on the finite specification. -/
theorem collarFiniteEnergyFactor_mul_exp_linkPositiveAction_le
    {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (sigma : Wilson.ContinuousUnitaryRepData G n)
    (E : Finset (PositiveEdge d))
    (U V : LinkReflection.SideConfiguration G
      (Lambda.linkPositiveEdges tau k))
    (hUV : ∀ p, p.1 ∉ E → U p = V p) :
    collarFiniteEnergyFactor beta sigma.wilsonPotential E *
        Real.exp (beta *
          (Lambda.linkWilsonDecomposition tau k hLambda sigma).positiveAction V) ≤
      Real.exp (beta *
        (Lambda.linkWilsonDecomposition tau k hLambda sigma).positiveAction U) := by
  change collarFiniteEnergyFactor beta sigma.wilsonPotential E *
      Real.exp (beta * ∑ p ∈ Lambda.linkPositivePlaquettes tau k,
        sigma.wilsonPotential
          (holonomy (Lambda.linkEvaluateSide tau k hLambda V) p.boundary)) ≤
    Real.exp (beta * ∑ p ∈ Lambda.linkPositivePlaquettes tau k,
      sigma.wilsonPotential
        (holonomy (Lambda.linkEvaluateSide tau k hLambda U) p.boundary))
  exact collarFiniteEnergyFactor_mul_exp_action_le hbeta
    sigma.wilsonPotential (Lambda.linkPositivePlaquettes tau k) E
    (Lambda.linkEvaluateSide tau k hLambda U)
    (Lambda.linkEvaluateSide tau k hLambda V)
    (fun e he ↦ linkEvaluateSide_eq_of_not_mem
      Lambda tau k hLambda E U V hUV e he)

end

end YangMills.Gluelump.OneLink
