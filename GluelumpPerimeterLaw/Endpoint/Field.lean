/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.CombLoops
import GluelumpPerimeterLaw.Endpoint.Normalization
import GluelumpPerimeterLaw.Endpoint.Reflection
import GluelumpPerimeterLaw.Endpoint.ScreeningForm
import GluelumpPerimeterLaw.Lie.GeneralizedAxialMap
import GluelumpPerimeterLaw.RepresentationTheory.UnitaryMatrix

/-!
# General center-neutral gluelump endpoint field

This file connects the algebraic screening intertwiner to the generalized
Lie-algebra axial map and the canonical transverse comb.  Its output is the
normalized, nonzero, local field used by the reflection-positivity engine.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory
open Representation

noncomputable section

universe u

variable {G A : Type u} {d m n N : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]

/-! ## Generalized axial local fields -/

/-- Compatibility between the real adjoint action used to construct the
generalized axial map and its complex-linear realization used by screening.
For the genuine complexified adjoint representation this is definitional
after restricting scalars. -/
def AxialAdjointCompatible
    (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) : Prop :=
  ∀ g X, D.adjoint g X = adj g X

/-- Apply a continuous multilinear form to generalized axial values of a
finite family of based loops. -/
def generalizedAxialTensorField
    (D : Lie.FaithfulActionAxialData G A N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ A) (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) where
  toContinuousMap :=
    ⟨fun Q ↦ F (fun i ↦ Lie.generalizedAxial D (holonomy Q (q i))), by
      apply F.coe_continuous.comp
      apply continuous_pi
      intro i
      exact (Lie.continuous_generalizedAxial D).comp
        (continuous_holonomy (q i))⟩
  support := basedLoopSupport q
  dependsOn_support := by
    intro Q R hQR
    apply congrArg F
    funext i
    apply congrArg (Lie.generalizedAxial D)
    apply holonomy_eq_of_eqOn_edgeSupport
    intro e he
    apply hQR e
    change e ∈ basedLoopSupport q
    rw [basedLoopSupport, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩

@[simp]
theorem generalizedAxialTensorField_apply
    (D : Lie.FaithfulActionAxialData G A N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ A) (Fin n → ℂ))
    (Q : Configuration d G) :
    generalizedAxialTensorField D q F Q =
      F (fun i ↦ Lie.generalizedAxial D (holonomy Q (q i))) :=
  rfl

/-- The unnormalized generalized axial field transforms as a Higgs field in
the dual Wilson representation. -/
theorem generalizedAxialTensorField_covariant
    (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual) :
    GaugeCovariantAt rho x
      (generalizedAxialTensorField D q
        (continuousScreeningMultilinearForm adj rho T)) := by
  intro g Q
  rw [generalizedAxialTensorField_apply,
    generalizedAxialTensorField_apply]
  have hpoint :
      (fun i ↦ Lie.generalizedAxial D
        (holonomy (gaugeTransform g Q) (q i))) =
      fun i ↦ adj (g x)
        (Lie.generalizedAxial D (holonomy Q (q i))) := by
    funext i
    rw [holonomy_loop_gaugeTransform, Lie.generalizedAxial_conj,
      hcompat]
  rw [hpoint, continuousScreeningMultilinearForm_equivariant]

/-! ## Spanning and detection -/

/-- Real spanning of a complex vector space implies complex spanning. -/
theorem complex_span_eq_top_of_real_span_eq_top
    (a : G → A) (hreal : Submodule.span ℝ (Set.range a) = ⊤) :
    Submodule.span ℂ (Set.range a) = ⊤ := by
  let L : Submodule ℂ A := Submodule.span ℂ (Set.range a)
  have hle : Submodule.span ℝ (Set.range a) ≤ L.restrictScalars ℝ :=
    Submodule.span_le.mpr fun y hy ↦ by
      rcases hy with ⟨g, rfl⟩
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [hreal] at hle
  exact Submodule.eq_top_iff'.mpr fun y ↦ hle trivial

/-- A nonzero screening intertwiner detects generalized axial values on a
pure tensor. -/
theorem screeningIntertwiner_detects_generalizedAxial
    (D : Lie.FaithfulActionAxialData G A N)
    (H : Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) :
    ∃ u : Fin m → G,
      continuousScreeningMultilinearForm adj rho T
        (fun i ↦ Lie.generalizedAxial D (u i)) ≠ 0 := by
  have hspanC : Submodule.span ℂ
      (Set.range (Lie.generalizedAxial D)) = ⊤ :=
    complex_span_eq_top_of_real_span_eq_top
      (Lie.generalizedAxial D)
      (Lie.span_range_generalizedAxial_eq_top D H)
  have hTlin : T.toLinearMap ≠ 0 := by
    intro hzero
    apply hT
    apply IntertwiningMap.ext
    exact hzero
  obtain ⟨u, hu⟩ := Lie.nonzero_on_pure_tensor_of_spans
    (a := Lie.generalizedAxial D) T.toLinearMap hTlin hspanC
  refine ⟨u, ?_⟩
  rw [continuousScreeningMultilinearForm_apply]
  intro hzero
  apply hu
  apply (dualCoordinates n).injective
  simpa using hzero

/-! ## The normalized comb endpoint `phi` -/

/-- The canonical normalized general gluelump endpoint.  It is built from
pure gauge holonomies and transforms exactly as a Higgs field in the dual
Wilson representation. -/
def phi
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) : LocalField d G (Fin n → ℂ) :=
  normalizedEndpoint
    (generalizedAxialTensorField D (combLoops (m := m) hd x)
      (continuousScreeningMultilinearForm adj rho T))

@[simp]
theorem phi_support
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) :
    (phi hd D adj rho T x).support =
      basedLoopSupport (combLoops (m := m) hd x) :=
  rfl

/-- The normalized field obeys the exact Higgs/dual-Wilson gauge law. -/
theorem phi_gauge_covariant
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) : GaugeCovariantAt rho x (phi hd D adj rho T x) :=
  (generalizedAxialTensorField_covariant D adj rho hcompat
    (combLoops (m := m) hd x) T).normalizedEndpoint rho x

/-- The canonical endpoint is pointwise normalized. -/
theorem phi_l2Norm_le_one
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (Q : Configuration d G) :
    endpointL2Norm (phi hd D adj rho T x Q) ≤ 1 :=
  normalizedEndpoint_l2Norm_le_one _ Q

/-- The canonical endpoint is not identically zero.  The witness is the
explicit sparse comb configuration; no gauge fixing or approximation enters
the proof. -/
theorem phi_not_identically_zero
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (H : Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d) :
    ∃ Q : Configuration d G, phi hd D adj rho T x Q ≠ 0 := by
  obtain ⟨u, hu⟩ :=
    screeningIntertwiner_detects_generalizedAxial D H adj rho T hT
  let Q : Configuration d G := combLoopConfiguration hd x u
  have hraw : generalizedAxialTensorField D
      (combLoops (m := m) hd x)
      (continuousScreeningMultilinearForm adj rho T) Q ≠ 0 := by
    rw [generalizedAxialTensorField_apply]
    have hargs :
        (fun i : Fin m ↦ Lie.generalizedAxial D
          (holonomy Q (combLoops hd x i))) =
        fun i ↦ Lie.generalizedAxial D (u i) := by
      funext i
      rw [combLoops_realize_holonomies]
    rw [hargs]
    exact hu
  exact ⟨Q, normalizedEndpoint_ne_at _ Q hraw⟩

/-- The endpoint collar lies entirely in the plane through its basepoint
perpendicular to the Wilson arm. -/
theorem phi_supportedInLinkPositiveHalf
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) :
    (phi hd D adj rho T x).SupportedInLinkPositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd) - 1) := by
  intro e he
  rw [phi_support] at he
  have hp := basedLoopSupport_combLoops_armPlane hd x e he
  omega

/-- The same transverse collar lies in the site-positive half-space whose
boundary contains the endpoint basepoint. -/
theorem phi_supportedInSitePositiveHalf
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) :
    (phi hd D adj rho T x).SupportedInSitePositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd)) := by
  intro e he
  rw [phi_support] at he
  have hp := basedLoopSupport_combLoops_armPlane hd x e he
  omega

/-- A translated copy of the canonical endpoint.  This is the copy constructor
used by straight-line and reflected endpoint families. -/
def phiTranslated
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (v x : Site d) : LocalField d G (Fin n → ℂ) :=
  (phi hd D adj rho T x).translatePullback v

@[simp]
theorem phiTranslated_apply
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (v x : Site d) (Q : Configuration d G) :
    phiTranslated hd D adj rho T v x Q =
      phi hd D adj rho T x
        (Gauge.LocalObservable.translateConfiguration v Q) :=
  rfl

/-- Translation moves the basepoint of the Higgs-field covariance law. -/
theorem phiTranslated_gauge_covariant
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (v x : Site d) :
    GaugeCovariantAt rho (Lattice.Cubic.translate v x)
      (phiTranslated hd D adj rho T v x) :=
  (phi_gauge_covariant hd D adj rho hcompat T x).translatePullback
    rho x (phi hd D adj rho T x) v

/-- The bond-reflected endpoint copy in precisely the form consumed by link
reflection positivity. -/
def phiLinkReflected
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (axis : Fin d) (cut : ℤ) :
    LocalField d G (Fin n → ℂ) :=
  (phi hd D adj rho T x).linkPullback axis cut

/-- Bond reflection moves the basepoint and preserves the Higgs-field law. -/
theorem phiLinkReflected_gauge_covariant
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (axis : Fin d) (cut : ℤ) :
    GaugeCovariantAt rho (linkReflection axis cut x)
      (phiLinkReflected hd D adj rho T x axis cut) :=
  (phi_gauge_covariant hd D adj rho hcompat T x).linkPullback
    rho x (phi hd D adj rho T x) axis cut

/-- The diagonally reflected endpoint copy used at a bending corner. -/
def phiDiagonalReflected
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) (axis₁ axis₂ : Fin d) (cut : ℤ) :
    LocalField d G (Fin n → ℂ) :=
  (phi hd D adj rho T x).diagonalPullback axis₁ axis₂ cut

/-- Diagonal reflection moves the basepoint and preserves the Higgs-field
law, with distinct axes as required by the geometric reflection. -/
theorem phiDiagonalReflected_gauge_covariant
    (hd : 3 ≤ d) (D : Lie.FaithfulActionAxialData G A N)
    (adj : Representation ℂ G A) (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj)
    (T : IntertwiningMap (tensorPower adj m) (asRepresentation rho).dual)
    (x : Site d) {axis₁ axis₂ : Fin d} (haxes : axis₁ ≠ axis₂)
    (cut : ℤ) :
    GaugeCovariantAt rho (diagonalReflection axis₁ axis₂ cut x)
      (phiDiagonalReflected hd D adj rho T x axis₁ axis₂ cut) :=
  (phi_gauge_covariant hd D adj rho hcompat T x).diagonalPullback
    rho x (phi hd D adj rho T x) haxes cut


end

end YangMills.Gluelump.Endpoint
