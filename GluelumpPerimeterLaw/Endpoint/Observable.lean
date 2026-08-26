/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Covariance

/-!
# Screened endpoint observables

Two dual endpoint fields can be contracted after transporting one of them
along a lattice path with the contragredient Wilson representation. The result
is an ordinary scalar `LocalObservable`, so all existing Gibbs, cluster, and
reflection APIs can consume it.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open scoped Matrix BigOperators

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Pointwise Hermitian contraction of a dual endpoint with the parallel
transport of a second dual endpoint. -/
def screenedValue (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G) : ℂ :=
  ∑ i, star (Phi A i) * dualAction rho (holonomy A gamma) (Psi A) i

/-- The source endpoint transported forward to the cutting site, written in
the common fiber at the cut.  The inverse is forced by the Hermitian
pairing convention. -/
def incomingHalfComponent (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ)) {x z : Site d}
    (p : Lattice.Cubic.Path x z) (i : Fin n) : LocalObservable d G where
  toContinuousMap := ⟨fun A =>
      dualAction rho (holonomy A p)⁻¹ (Phi A) i, by
    simp only [dualAction, Matrix.mulVec, dotProduct]
    apply continuous_finsetSum Finset.univ
    intro j _hj
    have hhol : Continuous (fun A : Configuration d G => holonomy A p) :=
      continuous_holonomy p
    have hinv : Continuous (fun A : Configuration d G => (holonomy A p)⁻¹) :=
      continuous_inv.comp hhol
    have hinvinv : Continuous (fun A : Configuration d G =>
        ((holonomy A p)⁻¹)⁻¹) := continuous_inv.comp hinv
    have hmatrix : Continuous (fun A : Configuration d G =>
        (rho.ρ ((holonomy A p)⁻¹)⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :=
      continuous_subtype_val.comp (rho.continuous_ρ.comp hinvinv)
    exact ((continuous_apply i).comp ((continuous_apply j).comp hmatrix)).mul
      ((continuous_apply j).comp Phi.toContinuousMap.continuous)⟩
  support := Phi.support ∪ p.edgeSupport
  dependsOn_support := by
    intro A B hAB
    have hPhi : Phi A = Phi B := Phi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_left _ he)
    have hp : holonomy A p = holonomy B p :=
      holonomy_eq_of_eqOn_edgeSupport p fun e he =>
        hAB e (Finset.mem_union_right _ he)
    change dualAction rho (holonomy A p)⁻¹ (Phi A) i =
      dualAction rho (holonomy B p)⁻¹ (Phi B) i
    rw [hPhi, hp]

/-- The target endpoint transported backward along the outgoing half to the
cutting site. -/
def outgoingHalfComponent (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ)) {z y : Site d}
    (q : Lattice.Cubic.Path z y) (i : Fin n) : LocalObservable d G where
  toContinuousMap := ⟨fun A =>
      dualAction rho (holonomy A q) (Psi A) i, by
    simp only [dualAction, Matrix.mulVec, dotProduct]
    apply continuous_finsetSum Finset.univ
    intro j _hj
    have hhol : Continuous (fun A : Configuration d G => holonomy A q) :=
      continuous_holonomy q
    have hinv : Continuous (fun A : Configuration d G => (holonomy A q)⁻¹) :=
      continuous_inv.comp hhol
    have hmatrix : Continuous (fun A : Configuration d G =>
        (rho.ρ (holonomy A q)⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :=
      continuous_subtype_val.comp (rho.continuous_ρ.comp hinv)
    exact ((continuous_apply i).comp ((continuous_apply j).comp hmatrix)).mul
      ((continuous_apply j).comp Psi.toContinuousMap.continuous)⟩
  support := Psi.support ∪ q.edgeSupport
  dependsOn_support := by
    intro A B hAB
    have hPsi : Psi A = Psi B := Psi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_left _ he)
    have hq : holonomy A q = holonomy B q :=
      holonomy_eq_of_eqOn_edgeSupport q fun e he =>
        hAB e (Finset.mem_union_right _ he)
    change dualAction rho (holonomy A q) (Psi A) i =
      dualAction rho (holonomy B q) (Psi B) i
    rw [hPsi, hq]

@[simp]
theorem incomingHalfComponent_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ)) {x z : Site d}
    (p : Lattice.Cubic.Path x z) (i : Fin n) (A : Configuration d G) :
    incomingHalfComponent rho Phi p i A =
      dualAction rho (holonomy A p)⁻¹ (Phi A) i :=
  rfl

@[simp]
theorem outgoingHalfComponent_apply
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ)) {z y : Site d}
    (q : Lattice.Cubic.Path z y) (i : Fin n) (A : Configuration d G) :
    outgoingHalfComponent rho Psi q i A =
      dualAction rho (holonomy A q) (Psi A) i :=
  rfl

/-- Cutting a screened line at any lattice site gives an exact finite Gram
sum over the representation index. -/
theorem screenedValue_comp_eq_halfGram
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x z y : Site d}
    (p : Lattice.Cubic.Path x z) (q : Lattice.Cubic.Path z y)
    (A : Configuration d G) :
    screenedValue rho Phi Psi (p.comp q) A =
      ∑ i, star (incomingHalfComponent rho Phi p i A) *
        outgoingHalfComponent rho Psi q i A := by
  have hpair := dualAction_pairing rho (holonomy A p)
    (dualAction rho (holonomy A p)⁻¹ (Phi A))
    (dualAction rho (holonomy A q) (Psi A))
  have hcancel : dualAction rho (holonomy A p)
      (dualAction rho (holonomy A p)⁻¹ (Phi A)) = Phi A := by
    rw [← dualAction_mul]
    simp
  rw [hcancel] at hpair
  unfold screenedValue
  rw [holonomy_comp, dualAction_mul]
  exact hpair

omit [IsTopologicalGroup G] in
theorem screenedValue_eq_hermitianPairing
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G) :
    screenedValue rho Phi Psi gamma A =
      hermitianPairing (Phi A)
        (dualAction rho (holonomy A gamma) (Psi A)) :=
  rfl

omit [IsTopologicalGroup G] in
/-- Pointwise Cauchy--Schwarz bound for a screened contraction. -/
theorem norm_screenedValue_le
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G) :
    ‖screenedValue rho Phi Psi gamma A‖ ≤
      endpointL2Norm (Phi A) * endpointL2Norm (Psi A) := by
  rw [screenedValue_eq_hermitianPairing]
  calc
    ‖hermitianPairing (Phi A)
        (dualAction rho (holonomy A gamma) (Psi A))‖ ≤
        endpointL2Norm (Phi A) *
          endpointL2Norm (dualAction rho (holonomy A gamma) (Psi A)) :=
      norm_hermitianPairing_le _ _
    _ = endpointL2Norm (Phi A) * endpointL2Norm (Psi A) := by
      rw [dualAction_l2Norm]

omit [IsTopologicalGroup G] in
/-- Normalized endpoints give a pointwise unit bound. -/
theorem norm_screenedValue_le_one
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G)
    (hPhi : endpointL2Norm (Phi A) ≤ 1)
    (hPsi : endpointL2Norm (Psi A) ≤ 1) :
    ‖screenedValue rho Phi Psi gamma A‖ ≤ 1 := by
  have hPsi0 : 0 ≤ endpointL2Norm (Psi A) := by
    unfold endpointL2Norm
    exact norm_nonneg _
  calc
    ‖screenedValue rho Phi Psi gamma A‖ ≤
        endpointL2Norm (Phi A) * endpointL2Norm (Psi A) :=
      norm_screenedValue_le rho Phi Psi gamma A
    _ ≤ 1 * 1 := mul_le_mul hPhi hPsi hPsi0 zero_le_one
    _ = 1 := one_mul 1

/-- The screened endpoint contraction as a scalar local observable. Its
support is exactly the recorded union of the two endpoint collars and the
transport path. -/
def screenedObservable (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) : LocalObservable d G where
  toContinuousMap := ⟨screenedValue rho Phi Psi gamma, by
    apply continuous_finsetSum Finset.univ
    intro i _hi
    apply (continuous_star.comp ((continuous_apply i).comp
      Phi.toContinuousMap.continuous)).mul
    simp only [dualAction, Matrix.mulVec, dotProduct]
    apply continuous_finsetSum Finset.univ
    intro j _hj
    have hhol : Continuous (fun A : Configuration d G => holonomy A gamma) :=
      continuous_holonomy gamma
    have hinv : Continuous (fun A : Configuration d G => (holonomy A gamma)⁻¹) :=
      continuous_inv.comp hhol
    have hmatrix : Continuous (fun A : Configuration d G =>
        (rho.ρ (holonomy A gamma)⁻¹ : Matrix (Fin n) (Fin n) ℂ)) :=
      continuous_subtype_val.comp (rho.continuous_ρ.comp hinv)
    exact ((continuous_apply i).comp ((continuous_apply j).comp hmatrix)).mul
      ((continuous_apply j).comp Psi.toContinuousMap.continuous)⟩
  support := Phi.support ∪ Psi.support ∪ gamma.edgeSupport
  dependsOn_support := by
    intro A B hAB
    have hPhi : Phi A = Phi B := Phi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
    have hPsi : Psi A = Psi B := Psi.dependsOn_support fun e he =>
      hAB e (Finset.mem_union_left _ (Finset.mem_union_right _ he))
    have hgamma : holonomy A gamma = holonomy B gamma :=
      holonomy_eq_of_eqOn_edgeSupport gamma fun e he =>
        hAB e (Finset.mem_union_right _ he)
    change screenedValue rho Phi Psi gamma A =
      screenedValue rho Phi Psi gamma B
    unfold screenedValue
    rw [hPhi, hPsi, hgamma]

@[simp]
theorem screenedObservable_apply (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G) :
    screenedObservable rho Phi Psi gamma A =
      screenedValue rho Phi Psi gamma A :=
  rfl

@[simp]
theorem screenedObservable_support (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) :
    (screenedObservable rho Phi Psi gamma).support =
      Phi.support ∪ Psi.support ∪ gamma.edgeSupport :=
  rfl

/-- Covariant endpoint fields make their screened contraction gauge
invariant.  This is the scalar bridge needed before applying any Gibbs or
reflection-positive expectation. -/
theorem screenedObservable_gaugeInvariant
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y)
    (hPhi : GaugeCovariantAt rho x Phi)
    (hPsi : GaugeCovariantAt rho y Psi) :
    IsGaugeInvariant (screenedObservable rho Phi Psi gamma) := by
  intro g A
  rw [screenedObservable_apply, screenedObservable_apply]
  unfold screenedValue
  rw [hPhi g A, hPsi g A, holonomy_gaugeTransform]
  have hcancel :
      dualAction rho (g y)⁻¹ (dualAction rho (g y) (Psi A)) = Psi A := by
    rw [← dualAction_mul]
    rw [show (g y)⁻¹ * g y = 1 by group, dualAction_one]
  have htransport :
      dualAction rho (g x * holonomy A gamma * (g y)⁻¹)
          (dualAction rho (g y) (Psi A)) =
        dualAction rho (g x)
          (dualAction rho (holonomy A gamma) (Psi A)) := by
    calc
      dualAction rho (g x * holonomy A gamma * (g y)⁻¹)
          (dualAction rho (g y) (Psi A)) =
          dualAction rho (g x * (holonomy A gamma * (g y)⁻¹))
            (dualAction rho (g y) (Psi A)) := by rw [mul_assoc]
      _ = dualAction rho (g x)
          (dualAction rho (holonomy A gamma * (g y)⁻¹)
            (dualAction rho (g y) (Psi A))) := dualAction_mul ..
      _ = dualAction rho (g x)
          (dualAction rho (holonomy A gamma)
            (dualAction rho (g y)⁻¹
              (dualAction rho (g y) (Psi A)))) := by rw [dualAction_mul]
      _ = dualAction rho (g x)
          (dualAction rho (holonomy A gamma) (Psi A)) := by
            rw [hcancel]
  rw [htransport]
  exact dualAction_pairing rho (g x) (Phi A)
    (dualAction rho (holonomy A gamma) (Psi A))

end

end YangMills.Gluelump.Endpoint
