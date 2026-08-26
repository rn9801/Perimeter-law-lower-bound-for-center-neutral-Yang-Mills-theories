/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Field
import GluelumpPerimeterLaw.OneLink.FixedVolumePower
import GluelumpPerimeterLaw.OneLink.ReflectedEndpointObservableCore

/-!
# Finite-volume positivity for a general screened endpoint

This file extracts the representation-free part of the existing one-link
argument from the older matrix-axial specialization.  The positive-side
endpoint is an arbitrary nonzero local covariant field.  In particular it can
be the projected generalized-axial field `Endpoint.phi`.

After the crossing bond is gauge fixed, the observable is the squared norm of
the full endpoint coordinate family.  Faithful matrix coordinates of the
Wilson action then detect a nonzero coordinate by Stone--Weierstrass.  The
selected-word estimate retains the endpoint coordinate inside the squared
Taylor amplitude.

The present repository kernel expands the crossing exponential into Taylor
Gram squares.  Consequently the completely formalized conclusion below is
strictness on a punctured neighborhood of `beta = 0`; the stronger all-positive
coupling statement from the roadmap would require a separate strictness
theorem for the interior-integrated exponential kernel.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint Propagation
open Filter Set
open scoped Matrix Topology

noncomputable section

universe u

variable {d n nsigma : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## An arbitrary reflected one-bond endpoint -/

/-- The positive-side coordinate family exposed after fixing the crossing
bond to the identity. -/
def reflectedEndpointOneLinkHalfFamily
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0) :
    Fin n → Gauge.LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Lambda.linkCrossingEdges tau 0) (Lambda.linkPositiveEdges tau 0) :=
  fun i ↦ linkRestrictNegativeObservable Lambda tau 0 hLambda
    (incomingHalfComponent rho (Psi.linkPullback tau 0)
      (reflectedIncomingPath tau 0 z hz
        (straightPositiveHalfPath tau z 0)) i)

/-- On the fixed crossing slice, the half family is exactly a coordinate of
the endpoint. -/
theorem reflectedEndpointOneLinkHalfFamily_fixedSlice_eq_endpoint
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0)
    (hPsi : Psi.SupportedInLinkPositiveHalf tau 0) (i : Fin n)
    (U : Gauge.LinkReflection.SideConfiguration G
      (Lambda.linkPositiveEdges tau 0)) :
    reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz i
        (1, U) =
      Psi (Lambda.linkEvaluateSide tau 0 hLambda U) i := by
  let q := straightPositiveHalfPath tau z 0
  have hq : Endpoint.Path.SupportedInLinkPositiveHalf tau 0 q :=
    straightPositiveHalfPath_supportedInLinkPositiveHalf tau 0 z hz 0
  obtain ⟨hin, _hout⟩ := reflectedFullPath_sideSupport
    rho Psi tau 0 z hz q hPsi hq
  have hside := linkRestrictNegative_reflectedIncoming_eq_outgoing_on_side
    Lambda tau 0 hLambda rho Psi z hz q i (hin i) U
  change linkRestrictNegativeObservable Lambda tau 0 hLambda
      (incomingHalfComponent rho (Psi.linkPullback tau 0)
        (reflectedIncomingPath tau 0 z hz q) i) (1, U) = _
  rw [hside]
  have hconfig :
      Lambda.evaluate (Lambda.linkAssemble tau 0 hLambda (1, (1, U))) =
        Lambda.linkEvaluateSide tau 0 hLambda U := rfl
  have hhol : holonomy (Lambda.linkEvaluateSide tau 0 hLambda U) q = 1 := rfl
  rw [hconfig]
  rw [outgoingHalfComponent_apply]
  rw [hhol, dualAction_one]

set_option maxHeartbeats 800000 in
-- The detector elaborates nested finite matrix sums and a Stone--Weierstrass
-- density argument, as does the older specialized theorem it generalizes.
/-- A nonzero local positive-side endpoint whose support is visible from
crossing plaquettes has a nonzero independent-Haar Taylor amplitude.  This is
the representation-free Stone--Weierstrass detector used for `phi` below. -/
theorem reflectedEndpointOneLink_exists_taylorAmplitude_zero_ne
    [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (hfaithful : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0)
    (hPsi : Psi.SupportedInLinkPositiveHalf tau 0)
    (hPsiNe : ∃ A, Psi A ≠ 0)
    (hcollarPositive : Psi.support ⊆ Lambda.linkPositiveEdges tau 0)
    (hvisible : ∀ e ∈ Psi.support,
      ∃ p : Lambda.linkCrossPlaquettes tau 0,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e) :
    ∃ (i : Fin n) (r : ℕ)
      (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
        (Lambda.linkCrossPlaquettes tau 0) nsigma r),
      (Lambda.linkWilsonDecomposition tau 0 hLambda sigma).taylorAmplitude
        0 (reflectedEndpointOneLinkHalfFamily
          Lambda tau hLambda rho Psi z hz i) w ≠ 0 := by
  classical
  let P := Lambda.linkPositiveEdges tau 0
  let S : Finset P := Finset.univ.filter fun e ↦ e.1 ∈ Psi.support
  have hplus (e : PositiveEdge d) (he : e ∈ Psi.support) :
      e ∈ Lambda.linkPositiveEdges tau 0 := hcollarPositive he
  have hsliceDep (i : Fin n) :
      DependsOn
        (fun U : Gauge.LinkReflection.SideConfiguration G P ↦
          reflectedEndpointOneLinkHalfFamily
            Lambda tau hLambda rho Psi z hz i (1, U))
        (S : Set P) := by
    intro U V hUV
    change reflectedEndpointOneLinkHalfFamily
        Lambda tau hLambda rho Psi z hz i (1, U) =
      reflectedEndpointOneLinkHalfFamily
        Lambda tau hLambda rho Psi z hz i (1, V)
    rw [reflectedEndpointOneLinkHalfFamily_fixedSlice_eq_endpoint
        Lambda tau hLambda rho Psi z hz hPsi i U,
      reflectedEndpointOneLinkHalfFamily_fixedSlice_eq_endpoint
        Lambda tau hLambda rho Psi z hz hPsi i V]
    apply congrFun
    apply Psi.dependsOn_support
    intro e he
    have he' : e ∈ Psi.support := by simpa using he
    let ep : P := ⟨e, hplus e he'⟩
    rw [Lambda.linkEvaluateSide_apply_of_mem tau 0 hLambda U e (hplus e he'),
      Lambda.linkEvaluateSide_apply_of_mem tau 0 hLambda V e (hplus e he')]
    apply hUV ep
    simp [S, ep, he']
  obtain ⟨A, hA⟩ := hPsiNe
  obtain ⟨i, hi⟩ : ∃ i : Fin n, Psi A i ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (funext h)
  let U : Gauge.LinkReflection.SideConfiguration G P := fun e ↦ A e.1
  have hPsiA : Psi (Lambda.linkEvaluateSide tau 0 hLambda U) = Psi A := by
    apply Psi.dependsOn_support
    intro e he
    rw [Lambda.linkEvaluateSide_apply_of_mem tau 0 hLambda U e (hplus e he)]
  have hsliceNe :
      (⟨fun V : Gauge.LinkReflection.SideConfiguration G P ↦
          reflectedEndpointOneLinkHalfFamily
            Lambda tau hLambda rho Psi z hz i (1, V),
        (reflectedEndpointOneLinkHalfFamily
          Lambda tau hLambda rho Psi z hz i).continuous.comp
            (continuous_const.prodMk continuous_id)⟩ : C(P → G, ℂ)) ≠ 0 := by
    intro hzero
    have hzU := DFunLike.congr_fun hzero U
    simp only [ContinuousMap.zero_apply] at hzU
    change reflectedEndpointOneLinkHalfFamily
      Lambda tau hLambda rho Psi z hz i (1, U) = 0 at hzU
    rw [reflectedEndpointOneLinkHalfFamily_fixedSlice_eq_endpoint
      Lambda tau hLambda rho Psi z hz hPsi i U] at hzU
    exact hi (hPsiA ▸ hzU)
  have hS_support (e : S) : e.1.1 ∈ Psi.support := by
    exact (Finset.mem_filter.mp e.2).2
  let q : S → Lambda.linkCrossPlaquettes tau 0 := fun e ↦
    Classical.choose (hvisible e.1.1 (hS_support e))
  have hq (e : S) :
      FiniteSpecification.linkCrossPositiveEdge tau (q e).1 = e.1.1 :=
    Classical.choose_spec (hvisible e.1.1 (hS_support e))
  let D := Lambda.linkWilsonDecomposition tau 0 hLambda sigma
  obtain ⟨r, w, hw⟩ := exists_taylorAmplitude_zero_ne_of_visible
    D hfaithful
    (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz i) S
    (hsliceDep i) hsliceNe q (by
      intro V e
      unfold D FiniteSpecification.linkWilsonDecomposition
      change Lambda.linkEvaluateSide tau 0 hLambda V
          (FiniteSpecification.linkCrossPositiveEdge tau (q e).1) = V e.1
      rw [hq e]
      exact Lambda.linkEvaluateSide_apply_of_mem tau 0 hLambda V
        e.1.1 e.1.2)
  exact ⟨i, r, w, hw⟩

/-- Exact gauge-fixed Gram-family identity for an arbitrary covariant
positive-side endpoint and its literal bond-reflected copy. -/
theorem reflectedEndpointOneLink_isGaugeFixedLinkFamilyNormSquare
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0)
    (hPsiCov : GaugeCovariantAt rho (step z (.forward tau)) Psi)
    (hPsi : Psi.SupportedInLinkPositiveHalf tau 0)
    (hdyn : (reflectedEndpointOneLinkObservable rho Psi tau z hz).support ⊆
      Lambda.dynamicEdges) :
    Lambda.IsGaugeFixedLinkFamilyPairing tau 0 hLambda
      (reflectedEndpointOneLinkObservable rho Psi tau z hz)
      (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz)
      (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz) := by
  let q := straightPositiveHalfPath tau z 0
  have hq : Endpoint.Path.SupportedInLinkPositiveHalf tau 0 q :=
    straightPositiveHalfPath_supportedInLinkPositiveHalf tau 0 z hz 0
  obtain ⟨hin, hout⟩ := reflectedFullPath_sideSupport
    rho Psi tau 0 z hz q hPsi hq
  have hedynamic : crossingPositiveEdge z tau ∈ Lambda.dynamicEdges := by
    apply hdyn
    simpa [reflectedEndpointOneLinkObservable, q] using
      (crossingPositiveEdge_mem_reflectedFullPath_support rho Psi tau z hz q)
  have hecross : crossingPositiveEdge z tau ∈ Lambda.linkCrossingEdges tau 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hedynamic, rfl, hz⟩
  simpa [reflectedEndpointOneLinkObservable,
    reflectedEndpointOneLinkHalfFamily, q] using
    (reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
      Lambda tau 0 hLambda rho Psi z hz q hPsiCov hdyn hecross hin hout)

/-- A selected Taylor word gives a positive summand lower bound for the full
screened endpoint expectation. -/
theorem reflectedEndpointOneLink_finite_selectedWord_lowerBound
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0) (hclosed : Lambda.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0)
    (hPsiCov : GaugeCovariantAt rho (step z (.forward tau)) Psi)
    (hPsi : Psi.SupportedInLinkPositiveHalf tau 0)
    (hdyn : (reflectedEndpointOneLinkObservable rho Psi tau z hz).support ⊆
      Lambda.dynamicEdges)
    {beta : ℝ} (hbeta : 0 ≤ beta) (i : Fin n) {r : ℕ}
    (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
      (Lambda.linkCrossPlaquettes tau 0) nsigma r) :
    (FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta)⁻¹ *
        (Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient
            (Lambda.linkWilsonDecomposition tau 0 hLambda sigma) beta r *
          ‖(Lambda.linkWilsonDecomposition tau 0 hLambda sigma).taylorAmplitude
              beta (reflectedEndpointOneLinkHalfFamily
                Lambda tau hLambda rho Psi z hz i) w‖ ^ 2) ≤
      Complex.re (∫ A, reflectedEndpointOneLinkObservable rho Psi tau z hz
          (Lambda.evaluate A)
        ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) := by
  apply
    Gauge.LinkReflection.FiniteSpecification.linkCrossingFamilyReflection_gibbsMeasure_selectedWord_lowerBound
    Lambda tau 0 hLambda hclosed sigma hbeta
    (reflectedEndpointOneLinkObservable rho Psi tau z hz)
    (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz)
    (reflectedEndpointOneLink_isGaugeFixedLinkFamilyNormSquare
      Lambda tau hLambda rho Psi z hz hPsiCov hPsi hdyn) i w

/-- One independent-Haar word gives a quantitative finite-volume power
lower bound. -/
theorem reflectedEndpointOneLink_finite_selectedWord_power_lowerBound
    (Lambda : FiniteSpecification d G) (tau : Fin d)
    (hLambda : Lambda.LinkSymmetric tau 0) (hclosed : Lambda.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z tau = 0)
    (hPsiCov : GaugeCovariantAt rho (step z (.forward tau)) Psi)
    (hPsi : Psi.SupportedInLinkPositiveHalf tau 0)
    (hdyn : (reflectedEndpointOneLinkObservable rho Psi tau z hz).support ⊆
      Lambda.dynamicEdges)
    (i : Fin n) {r : ℕ}
    (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
      (Lambda.linkCrossPlaquettes tau 0) nsigma r)
    (hw : (Lambda.linkWilsonDecomposition tau 0 hLambda sigma).taylorAmplitude
      0 (reflectedEndpointOneLinkHalfFamily
        Lambda tau hLambda rho Psi z hz i) w ≠ 0) :
    ∃ c > 0, ∃ beta0 > 0, ∀ beta, 0 < beta → beta ≤ beta0 →
      c * beta ^ r ≤ Complex.re
        (∫ A, reflectedEndpointOneLinkObservable rho Psi tau z hz
            (Lambda.evaluate A)
          ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) := by
  let D := Lambda.linkWilsonDecomposition tau 0 hLambda sigma
  let F := reflectedEndpointOneLinkHalfFamily Lambda tau hLambda rho Psi z hz i
  let Z : ℝ → ℝ := fun beta ↦
    FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta
  let K : ℝ := ((2 * nsigma : ℝ)⁻¹) ^ r / r.factorial
  let h : ℝ → ℝ := fun beta ↦
    (Z beta)⁻¹ * K * ‖D.taylorAmplitude beta F w‖ ^ 2
  have hZcont : Continuous Z := by
    simpa [Z] using FiniteVolume.continuous_partitionFunction
      Lambda sigma.wilsonPotential
  have hZzero : Z 0 = 1 := by simp [Z]
  have hh : ContinuousAt h 0 := by
    have hinv : ContinuousAt (fun beta ↦ (Z beta)⁻¹) 0 :=
      hZcont.continuousAt.inv₀ (by simp [hZzero])
    have hamp : Continuous fun beta ↦ ‖D.taylorAmplitude beta F w‖ ^ 2 :=
      (D.continuous_taylorAmplitude F w).norm.pow 2
    exact (hinv.mul continuousAt_const).mul hamp.continuousAt
  have hK : 0 < K := by
    dsimp [K]
    positivity [sigma.dimension_pos]
  have hh0 : 0 < h 0 := by
    dsimp [h]
    rw [hZzero]
    simp only [inv_one, one_mul]
    exact mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr hw))
  obtain ⟨c, hc, beta0, hbeta0, hlower⟩ :=
    power_lower_bound_of_continuous_factor r hh hh0
  refine ⟨c, hc, beta0, hbeta0, fun beta hbeta hbetaLe ↦ ?_⟩
  have hselected := reflectedEndpointOneLink_finite_selectedWord_lowerBound
    Lambda tau hLambda hclosed sigma rho Psi z hz hPsiCov hPsi hdyn
      hbeta.le i w
  apply (hlower beta hbeta hbetaLe).trans
  calc
    beta ^ r * h beta =
        (FiniteVolume.partitionFunction Lambda sigma.wilsonPotential beta)⁻¹ *
          (Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient
              D beta r * ‖D.taylorAmplitude beta F w‖ ^ 2) := by
      simp only [h, Z, K,
        Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient]
      rw [div_pow, inv_pow]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by simpa [D, F] using hselected

/-! ## The canonical generalized-axial endpoint -/

variable {A : Type u} {m N : ℕ}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]

/-- The roadmap's finite-volume output for the normalized generalized-axial
endpoint.  The exponent and coefficient may depend on the finite
specification, while the endpoint factor is retained in the selected
amplitude.  Strong coupling is used only to obtain the displayed interval.

The stronger claim of strictness for every positive coupling requires the
separate exponential-kernel theorem described in the module docstring. -/
theorem exists_generalPhi_reflectedOneLink_finite_power_lowerBound
    [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (Lambda : FiniteSpecification d G) (hd : 3 ≤ d)
    (hLambda : Lambda.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Lambda.PlaquetteClosed)
    (D : Lie.FaithfulActionAxialData G A N)
    (H : Lie.AxialFirstOrderData D)
    (adj : Representation ℂ G A)
    (rho : ContinuousUnitaryRepData G n)
    (hcompat : AxialAdjointCompatible D adj)
    (T : Representation.IntertwiningMap
      (RepresentationTheory.tensorPower adj m)
      (RepresentationTheory.asRepresentation rho).dual)
    (hT : T ≠ 0)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (reflectedEndpointOneLinkObservable rho
        (phi hd D adj rho T
          (step z (.forward (Geometry.armAxis hd))))
        (Geometry.armAxis hd) z hz).support ⊆ Lambda.dynamicEdges)
    (hactive : ∀ p : Plaquette d,
      p.base (Geometry.armAxis hd) = 0 →
      (p.first = Geometry.armAxis hd ∨ p.second = Geometry.armAxis hd) →
      p ∈ Lambda.activePlaquettes) :
    ∃ (r : ℕ) (c beta0 : ℝ), 0 < c ∧ 0 < beta0 ∧
      ∀ beta, 0 < beta → beta ≤ beta0 →
        c * beta ^ r ≤ Complex.re
          (∫ Q, reflectedEndpointOneLinkObservable rho
              (phi hd D adj rho T
                (step z (.forward (Geometry.armAxis hd))))
              (Geometry.armAxis hd) z hz (Lambda.evaluate Q)
            ∂FiniteVolume.gibbsMeasure Lambda D.sigma.wilsonPotential beta) := by
  let tau := Geometry.armAxis hd
  let x := step z (.forward tau)
  let Psi := phi hd D adj rho T x
  let O := reflectedEndpointOneLinkObservable rho Psi tau z hz
  have hx : x tau = 1 := by
    simp [x, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hcut : x tau - 1 = 0 := by omega
  have hPsi : Psi.SupportedInLinkPositiveHalf tau 0 := by
    simpa [Psi, tau, hcut] using
      phi_supportedInLinkPositiveHalf hd D adj rho T x
  have hPsiCov : GaugeCovariantAt rho (step z (.forward tau)) Psi := by
    simpa [Psi, x] using phi_gauge_covariant hd D adj rho hcompat T x
  have hPsiNe : ∃ Q, Psi Q ≠ 0 := by
    simpa [Psi] using phi_not_identically_zero hd D H adj rho T hT x
  have hcollarDyn : Psi.support ⊆ Lambda.dynamicEdges := by
    intro e he
    apply hdyn
    change e ∈ O.support
    rw [show O = reflectedEndpointOneLinkObservable rho Psi tau z hz by rfl]
    rw [reflectedEndpointOneLinkObservable, screenedObservable_support]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
  have hcollarPositive : Psi.support ⊆ Lambda.linkPositiveEdges tau 0 := by
    intro e he
    rw [FiniteSpecification.linkPositiveEdges, Finset.mem_filter]
    refine ⟨hcollarDyn he, ?_⟩
    have hp : e.source tau = x tau := by
      rw [show Psi.support = basedLoopSupport (combLoops (m := m) hd x) by
        simp [Psi]] at he
      exact (basedLoopSupport_combLoops_armPlane hd x e he).1
    rw [hp, hx]
    norm_num
  have hvisible : ∀ e ∈ Psi.support,
      ∃ p : Lambda.linkCrossPlaquettes tau 0,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e := by
    intro e he
    apply transverseLoop_support_has_linkCrossPlaquette
      Lambda hd x 0 (by simpa [hx]) hactive e
    simpa [Psi] using he
  obtain ⟨i, r, w, hw⟩ :=
    reflectedEndpointOneLink_exists_taylorAmplitude_zero_ne
      Lambda tau hLambda D.sigma D.faithful rho Psi z hz hPsi hPsiNe
        hcollarPositive hvisible
  obtain ⟨c, hc, beta0, hbeta0, hlower⟩ :=
    reflectedEndpointOneLink_finite_selectedWord_power_lowerBound
      Lambda tau hLambda hclosed D.sigma rho Psi z hz hPsiCov hPsi
        (by simpa [O] using hdyn) i w hw
  exact ⟨r, c, beta0, hc, hbeta0, by simpa [Psi, tau] using hlower⟩

end

end YangMills.Gluelump.OneLink
