/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.CombLoops
import GluelumpPerimeterLaw.Endpoint.Normalization
import GluelumpPerimeterLaw.Endpoint.Reflection
import GluelumpPerimeterLaw.Endpoint.ScreeningForm
import GluelumpPerimeterLaw.RepresentationTheory.CenterScreening

/-!
# Direct conjugation-span gluelump endpoint

The endpoint in this file uses the representation matrices of actual loop
holonomies directly.  No logarithm, local chart, Lie algebra, or axial map is
involved.  A nonzero tensor-power intertwiner is evaluated on the pure tensor
of the comb holonomies and the result is canonically normalized.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory
open Representation

noncomputable section

variable {G : Type*} {d m n p : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-! ## The literal representation-matrix source -/

/-- An actual representation matrix, regarded as an element of its literal
conjugation span. -/
def sigmaInConjSpan (sigma : ContinuousUnitaryRepData G n) (g : G) :
    ConjSpan sigma :=
  ⟨sigma.ρ g, sigma_mem_conjSpan sigma g⟩

@[simp]
theorem sigmaInConjSpan_coe
    (sigma : ContinuousUnitaryRepData G n) (g : G) :
    (sigmaInConjSpan sigma g : Matrix (Fin n) (Fin n) ℂ) = sigma.ρ g :=
  rfl

/-- The literal source map is continuous in the inherited finite-dimensional
matrix topology. -/
theorem continuous_sigmaInConjSpan
    (sigma : ContinuousUnitaryRepData G n) :
    Continuous (sigmaInConjSpan sigma) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp sigma.continuous_ρ

/-- Conjugating a group element acts on its literal matrix by the restricted
conjugation-span representation. -/
theorem sigmaInConjSpan_conj
    (sigma : ContinuousUnitaryRepData G n) (g h : G) :
    sigmaInConjSpan sigma (g * h * g⁻¹) =
      conjSpanRep sigma g (sigmaInConjSpan sigma h) := by
  apply Subtype.ext
  simp only [sigmaInConjSpan_coe, conjSpanRep_apply_coe, map_mul,
    Matrix.UnitaryGroup.mul_val]

/-- The actual representation matrices span the literal conjugation-span
carrier, including after they are packaged as subtype elements. -/
theorem span_range_sigmaInConjSpan_eq_top
    (sigma : ContinuousUnitaryRepData G n) :
    Submodule.span ℂ (Set.range (sigmaInConjSpan sigma)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff
    (ConjSpan sigma) (sigma_mem_conjSpan sigma)).2
  rfl

/-- The same literal matrix in the Hilbert--Schmidt copy used to supply the
finite-dimensional normed topology. -/
def sigmaInHilbertConjSpan
    (sigma : ContinuousUnitaryRepData G n) (g : G) :
    HilbertConjSpan sigma :=
  conjSpanHilbertEquiv sigma (sigmaInConjSpan sigma g)

/-- The Hilbert--Schmidt copy of the literal source map is continuous. -/
theorem continuous_sigmaInHilbertConjSpan
    (sigma : ContinuousUnitaryRepData G n) :
    Continuous (sigmaInHilbertConjSpan sigma) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n => PiLp 2 (fun _ : Fin n => ℂ))).comp
  apply continuous_pi
  intro i
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro j
  exact ((continuous_subtype_val.comp sigma.continuous_ρ).matrix_elem i j)

/-- Conjugation covariance in the Hilbert--Schmidt copy. -/
theorem sigmaInHilbertConjSpan_conj
    (sigma : ContinuousUnitaryRepData G n) (g h : G) :
    sigmaInHilbertConjSpan sigma (g * h * g⁻¹) =
      hilbertConjSpanRep sigma g (sigmaInHilbertConjSpan sigma h) := by
  apply (conjSpanHilbertEquiv sigma).symm.injective
  simp only [sigmaInHilbertConjSpan, LinearEquiv.symm_apply_apply,
    conjSpanHilbertEquiv_symm_hilbertConjSpanRep]
  exact sigmaInConjSpan_conj sigma g h

/-- Transport the operational intertwiner from the literal subtype to its
linearly equivalent Hilbert--Schmidt copy. -/
def hilbertConjSpanScreeningIntertwiner
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual) :
    IntertwiningMap (tensorPower (hilbertConjSpanRep sigma) m)
      (asRepresentation rho).dual :=
  T.comp (Representation.Equiv.toIntertwiningMap
    (tensorPowerEquiv (conjSpanHilbertRepEquiv sigma) m).symm)

/-- The continuous screening form specialized to the literal conjugation
span.  Recording this specialization keeps subsequent elaboration narrow. -/
def conjSpanScreeningForm
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) (Fin p → ℂ) :=
  continuousScreeningMultilinearForm (hilbertConjSpanRep sigma) rho
    (hilbertConjSpanScreeningIntertwiner sigma rho T)

@[simp]
theorem conjSpanScreeningForm_apply
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual) (v : Fin m → HilbertConjSpan sigma) :
    conjSpanScreeningForm sigma rho T v =
      dualCoordinates p ((hilbertConjSpanScreeningIntertwiner sigma rho T)
        (PiTensorProduct.tprod ℂ v)) :=
  continuousScreeningMultilinearForm_apply
    (hilbertConjSpanRep sigma) rho
      (hilbertConjSpanScreeningIntertwiner sigma rho T) v

theorem conjSpanScreeningForm_equivariant
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual) (g : G)
    (v : Fin m → HilbertConjSpan sigma) :
    conjSpanScreeningForm sigma rho T
        (fun i ↦ hilbertConjSpanRep sigma g (v i)) =
      dualAction rho g (conjSpanScreeningForm sigma rho T v) :=
  continuousScreeningMultilinearForm_equivariant
    (hilbertConjSpanRep sigma) rho
      (hilbertConjSpanScreeningIntertwiner sigma rho T) g v

/-! ## Direct holonomy tensor field -/

/-- Apply a continuous multilinear form directly to the representation
matrices of a finite family of based loop holonomies. -/
def conjSpanTensorField
    (sigma : ContinuousUnitaryRepData G n) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) (Fin p → ℂ)) :
    LocalField d G (Fin p → ℂ) where
  toContinuousMap :=
    ⟨fun Q ↦ F (fun i ↦ sigmaInHilbertConjSpan sigma (holonomy Q (q i))), by
      apply F.coe_continuous.comp
      apply continuous_pi
      intro i
      exact (continuous_sigmaInHilbertConjSpan sigma).comp
        (continuous_holonomy (q i))⟩
  support := basedLoopSupport q
  dependsOn_support := by
    intro Q R hQR
    apply congrArg F
    funext i
    apply congrArg (sigmaInHilbertConjSpan sigma)
    apply holonomy_eq_of_eqOn_edgeSupport
    intro e he
    apply hQR e
    change e ∈ basedLoopSupport q
    rw [basedLoopSupport, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩

@[simp]
theorem conjSpanTensorField_apply
    (sigma : ContinuousUnitaryRepData G n) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (F : ContinuousMultilinearMap ℂ
      (fun _ : Fin m ↦ HilbertConjSpan sigma) (Fin p → ℂ))
    (Q : Configuration d G) :
    conjSpanTensorField sigma q F Q =
      F (fun i ↦ sigmaInHilbertConjSpan sigma (holonomy Q (q i))) :=
  rfl

/-- The direct unnormalized field obeys the exact dual-Wilson gauge law. -/
theorem conjSpanTensorField_covariant
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual) :
    GaugeCovariantAt rho x
      (conjSpanTensorField sigma q
        (conjSpanScreeningForm sigma rho T)) := by
  intro g Q
  rw [conjSpanTensorField_apply, conjSpanTensorField_apply]
  have hpoint :
      (fun i ↦ sigmaInHilbertConjSpan sigma
        (holonomy (gaugeTransform g Q) (q i))) =
      fun i ↦ hilbertConjSpanRep sigma (g x)
        (sigmaInHilbertConjSpan sigma (holonomy Q (q i))) := by
    funext i
    rw [holonomy_loop_gaugeTransform, sigmaInHilbertConjSpan_conj]
  rw [hpoint, conjSpanScreeningForm_equivariant]

/-! ## Pure-holonomy detection -/

/-- A nonzero conjugation-span screening intertwiner is nonzero on a pure
tensor of actual representation matrices. -/
theorem screeningIntertwiner_detects_sigmaInConjSpan
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (hT : T ≠ 0) :
    ∃ u : Fin m → G,
      conjSpanScreeningForm sigma rho T
        (fun i ↦ sigmaInHilbertConjSpan sigma (u i)) ≠ 0 := by
  have hTlin : T.toLinearMap ≠ 0 := by
    intro hzero
    apply hT
    apply IntertwiningMap.ext
    exact hzero
  obtain ⟨u, hu⟩ := nonzero_on_pure_tensor_of_spans
    (K := ℂ) (V := ConjSpan sigma)
    (W := Module.Dual ℂ (Fin p → ℂ)) (I := G) (r := m)
    (a := sigmaInConjSpan sigma) T.toLinearMap hTlin
      (span_range_sigmaInConjSpan_eq_top sigma)
  refine ⟨u, ?_⟩
  intro hzero
  apply hu
  rw [conjSpanScreeningForm_apply] at hzero
  have htransport :
      (tensorPowerEquiv (conjSpanHilbertRepEquiv sigma) m).symm.toLinearEquiv
          (PiTensorProduct.tprod ℂ
            (fun i ↦ sigmaInHilbertConjSpan sigma (u i))) =
        PiTensorProduct.tprod ℂ (fun i ↦ sigmaInConjSpan sigma (u i)) := by
    change (PiTensorProduct.congr
      (fun _ : Fin m ↦ conjSpanHilbertEquiv sigma)).symm
        (PiTensorProduct.tprod ℂ
          (fun i ↦ sigmaInHilbertConjSpan sigma (u i))) = _
    rw [PiTensorProduct.congr_symm_tprod]
    simp [sigmaInHilbertConjSpan]
  change dualCoordinates p
      (T ((tensorPowerEquiv
        (conjSpanHilbertRepEquiv sigma) m).symm.toLinearEquiv
          (PiTensorProduct.tprod ℂ
            (fun i ↦ sigmaInHilbertConjSpan sigma (u i))))) = 0 at hzero
  rw [htransport] at hzero
  apply (dualCoordinates p).injective
  simpa using hzero

/-! ## The normalized comb endpoint -/

/-- The canonical normalized endpoint built directly from comb-loop
holonomies in the conjugation span. -/
def conjSpanPhi
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) : LocalField d G (Fin p → ℂ) :=
  normalizedEndpoint
    (conjSpanTensorField sigma (combLoops (m := m) hd x)
      (conjSpanScreeningForm sigma rho T))

@[simp]
theorem conjSpanPhi_support
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) :
    (conjSpanPhi hd sigma rho T x).support =
      basedLoopSupport (combLoops (m := m) hd x) :=
  rfl

/-- The normalized direct endpoint obeys the exact Higgs/dual-Wilson gauge
law. -/
theorem conjSpanPhi_gauge_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) : GaugeCovariantAt rho x (conjSpanPhi hd sigma rho T x) :=
  (conjSpanTensorField_covariant sigma rho
    (combLoops (m := m) hd x) T).normalizedEndpoint rho x

/-- The normalized direct endpoint has pointwise Euclidean norm at most one. -/
theorem conjSpanPhi_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (Q : Configuration d G) :
    endpointL2Norm (conjSpanPhi hd sigma rho T x Q) ≤ 1 :=
  normalizedEndpoint_l2Norm_le_one _ Q

/-- The normalized direct endpoint is not identically zero.  Its witness is
the explicit sparse comb configuration realizing the detected holonomies. -/
theorem conjSpanPhi_not_identically_zero
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (hT : T ≠ 0) (x : Site d) :
    ∃ Q : Configuration d G, conjSpanPhi hd sigma rho T x Q ≠ 0 := by
  obtain ⟨u, hu⟩ :=
    screeningIntertwiner_detects_sigmaInConjSpan sigma rho T hT
  let Q : Configuration d G := combLoopConfiguration hd x u
  have hraw : conjSpanTensorField sigma
      (combLoops (m := m) hd x)
      (conjSpanScreeningForm sigma rho T) Q ≠ 0 := by
    rw [conjSpanTensorField_apply]
    have hargs :
        (fun i : Fin m ↦ sigmaInHilbertConjSpan sigma
          (holonomy Q (combLoops hd x i))) =
        fun i ↦ sigmaInHilbertConjSpan sigma (u i) := by
      funext i
      rw [combLoops_realize_holonomies]
    rw [hargs]
    exact hu
  exact ⟨Q, normalizedEndpoint_ne_at _ Q hraw⟩

/-! ## Support half-spaces and canonical copies -/

/-- The direct endpoint collar lies in the plane through its basepoint
perpendicular to the Wilson arm. -/
theorem conjSpanPhi_supportedInLinkPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) :
    (conjSpanPhi hd sigma rho T x).SupportedInLinkPositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd) - 1) := by
  intro e he
  rw [conjSpanPhi_support] at he
  have hp := basedLoopSupport_combLoops_armPlane hd x e he
  omega

/-- The same collar lies in the site-positive half-space based at the
endpoint. -/
theorem conjSpanPhi_supportedInSitePositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) :
    (conjSpanPhi hd sigma rho T x).SupportedInSitePositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd)) := by
  intro e he
  rw [conjSpanPhi_support] at he
  have hp := basedLoopSupport_combLoops_armPlane hd x e he
  omega

/-- A translated copy of the direct endpoint. -/
def conjSpanPhiTranslated
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (v x : Site d) : LocalField d G (Fin p → ℂ) :=
  (conjSpanPhi hd sigma rho T x).translatePullback v

@[simp]
theorem conjSpanPhiTranslated_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (v x : Site d) (Q : Configuration d G) :
    conjSpanPhiTranslated hd sigma rho T v x Q =
      conjSpanPhi hd sigma rho T x
        (Gauge.LocalObservable.translateConfiguration v Q) :=
  rfl

theorem conjSpanPhiTranslated_gauge_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (v x : Site d) :
    GaugeCovariantAt rho (Lattice.Cubic.translate v x)
      (conjSpanPhiTranslated hd sigma rho T v x) :=
  (conjSpanPhi_gauge_covariant hd sigma rho T x).translatePullback
    rho x (conjSpanPhi hd sigma rho T x) v

/-- The bond-reflected direct endpoint copy. -/
def conjSpanPhiLinkReflected
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (axis : Fin d) (cut : ℤ) :
    LocalField d G (Fin p → ℂ) :=
  (conjSpanPhi hd sigma rho T x).linkPullback axis cut

theorem conjSpanPhiLinkReflected_gauge_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (axis : Fin d) (cut : ℤ) :
    GaugeCovariantAt rho (linkReflection axis cut x)
      (conjSpanPhiLinkReflected hd sigma rho T x axis cut) :=
  (conjSpanPhi_gauge_covariant hd sigma rho T x).linkPullback
    rho x (conjSpanPhi hd sigma rho T x) axis cut

/-- The diagonally reflected direct endpoint copy. -/
def conjSpanPhiDiagonalReflected
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (axis₁ axis₂ : Fin d) (cut : ℤ) :
    LocalField d G (Fin p → ℂ) :=
  (conjSpanPhi hd sigma rho T x).diagonalPullback axis₁ axis₂ cut

theorem conjSpanPhiDiagonalReflected_gauge_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) {axis₁ axis₂ : Fin d} (haxes : axis₁ ≠ axis₂)
    (cut : ℤ) :
    GaugeCovariantAt rho (diagonalReflection axis₁ axis₂ cut x)
      (conjSpanPhiDiagonalReflected hd sigma rho T x axis₁ axis₂ cut) :=
  (conjSpanPhi_gauge_covariant hd sigma rho T x).diagonalPullback
    rho x (conjSpanPhi hd sigma rho T x) haxes cut

end

end YangMills.Gluelump.Endpoint
