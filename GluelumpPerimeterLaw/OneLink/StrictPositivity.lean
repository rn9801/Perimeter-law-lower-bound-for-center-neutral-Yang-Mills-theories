/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.LinkReflectionStrictPositivity
import GluelumpPerimeterLaw.OneLink.TransversePrism
import GluelumpPerimeterLaw.OneLink.WordDetection
import GluelumpPerimeterLaw.Propagation.StraightGeometry

/-!
# Strict positivity for the one-link screened observable

The screened representation `rho` and the Wilson-action representation
`sigma` are deliberately separate.  After the crossing link is gauge fixed,
the complete vector endpoint is a finite Gram family.  One nonzero Taylor
amplitude in that family gives strict positivity of the normalized one-link
expectation; no endpoint factor is discarded.

For the explicit transverse endpoint, `TransversePrism` supplies the geometric
reason that such an amplitude can be built from crossing plaquettes: it uses
two axes perpendicular to the arm and hence genuinely requires `3 ≤ d`.
The remaining existence of a detected word is the faithful-action
Stone--Weierstrass/spin-network input.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint
open Propagation
open Filter Set
open scoped Matrix Topology

noncomputable section

variable {d m n N nsigma : ℕ} {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The explicit finite family on the negative half of the one-link cut.
Its coordinates retain the endpoint factor which would be lost by an early
scalar contraction. -/
def transverseOneLinkHalfFamily
    (Λ : FiniteSpecification d G)
    (hd : 3 ≤ d) (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) :
    Fin n → Gauge.LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges (Geometry.armAxis hd) 0)
      (Λ.linkPositiveEdges (Geometry.armAxis hd) 0) :=
  let tau := Geometry.armAxis hd
  let Psi := transverseStraightArmEndpoint hd eta T z 0
  fun i => linkRestrictNegativeObservable Λ tau 0 hΛ
    (incomingHalfComponent rho (Psi.linkPullback tau 0)
      (reflectedIncomingPath tau 0 z hz
        (straightPositiveHalfPath tau z 0)) i)

/-- On the gauge-fixed side, the zero-length one-link half family is exactly
one coordinate of the transverse endpoint. -/
theorem transverseOneLinkHalfFamily_fixedSlice_eq_endpoint
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (i : Fin n)
    (U : LinkReflection.SideConfiguration G
      (Λ.linkPositiveEdges (Geometry.armAxis hd) 0)) :
    transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, U) =
      transverseStraightArmEndpoint hd eta T z 0
        (Λ.linkEvaluateSide (Geometry.armAxis hd) 0 hΛ U) i := by
  let tau := Geometry.armAxis hd
  let Psi := transverseStraightArmEndpoint hd eta T z 0
  let q := straightPositiveHalfPath tau z 0
  have htarget : Path.advance (step z (.forward tau)) (.forward tau) 0 =
      step z (.forward tau) := by simp [Path.advance_eq]
  have hPsi : Psi.SupportedInLinkPositiveHalf tau 0 := by
    simpa [Psi, transverseStraightArmEndpoint, tau, htarget, hz, step,
      SignedDirection.forward, SignedDirection.delta, unitVector] using
      (transverseAxialEndpoint_supportedInLinkPositiveHalf hd eta
        (step z (.forward tau)) T)
  have hq : Endpoint.Path.SupportedInLinkPositiveHalf tau 0 q :=
    straightPositiveHalfPath_supportedInLinkPositiveHalf tau 0 z hz 0
  obtain ⟨hin, _hout⟩ := reflectedFullPath_sideSupport
    rho Psi tau 0 z hz q hPsi hq
  have hside := linkRestrictNegative_reflectedIncoming_eq_outgoing_on_side
    Λ tau 0 hΛ rho Psi z hz q i (hin i) U
  change linkRestrictNegativeObservable Λ tau 0 hΛ
      (incomingHalfComponent rho (Psi.linkPullback tau 0)
        (reflectedIncomingPath tau 0 z hz q) i) (1, U) = _
  rw [hside]
  have hconfig :
      Λ.evaluate (Λ.linkAssemble tau 0 hΛ (1, (1, U))) =
        Λ.linkEvaluateSide tau 0 hΛ U := rfl
  have hhol : holonomy (Λ.linkEvaluateSide tau 0 hΛ U) q = 1 := rfl
  rw [hconfig]
  rw [outgoingHalfComponent_apply]
  rw [hhol, dualAction_one]

set_option maxHeartbeats 800000 in
-- The finite Stone--Weierstrass detector expands several nested matrix sums;
-- elaborating this proof needs more than the project-wide default.
/-- Faithfulness and visibility of the transverse collar by cross plaquettes
produce an actual nonzero Taylor word.  The endpoint nonvanishing hypothesis
is the concrete axial-map condition; no irreducible decomposition is used. -/
theorem transverseOneLink_exists_taylorAmplitude_zero_ne
    [MeasureTheory.Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (hfaithful : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hendpoint : ∃ u : Fin m → G,
      T (fun j => Lie.axialMatrix eta (u j)) ≠ 0)
    (hcollarDyn : basedLoopSupport
      (transverseLoop (m := m) hd
        (step z (.forward (Geometry.armAxis hd)))) ⊆ Λ.dynamicEdges)
    (hvisiblePrism : ∀ e ∈ basedLoopSupport
      (transverseLoop (m := m) hd
        (step z (.forward (Geometry.armAxis hd)))),
      ∃ p : Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0,
        FiniteSpecification.linkCrossPositiveEdge
          (Geometry.armAxis hd) p.1 = e) :
    ∃ (i : Fin n) (r : ℕ)
      (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
        (Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0) nsigma r),
      (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma).taylorAmplitude
        0 (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i) w ≠ 0 := by
  classical
  let tau := Geometry.armAxis hd
  let x := step z (.forward tau)
  let Psi := transverseStraightArmEndpoint hd eta T z 0
  let collar := basedLoopSupport (transverseLoop (m := m) hd x)
  let P := Λ.linkPositiveEdges tau 0
  let S : Finset P := Finset.univ.filter fun e => e.1 ∈ collar
  have hx : x tau = 1 := by
    simp [x, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hplus (e : PositiveEdge d) (he : e ∈ collar) :
      e ∈ Λ.linkPositiveEdges tau 0 := by
    rw [FiniteSpecification.linkPositiveEdges, Finset.mem_filter]
    refine ⟨hcollarDyn he, ?_⟩
    have hplane := basedLoopSupport_transverseLoop_armPlane hd x e he
    rw [hplane.1, hx]
    omega
  have hsliceDep (i : Fin n) :
      DependsOn
        (fun U : LinkReflection.SideConfiguration G P =>
          transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, U))
        (S : Set P) := by
    intro U V hUV
    change transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, U) =
      transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, V)
    rw [transverseOneLinkHalfFamily_fixedSlice_eq_endpoint,
      transverseOneLinkHalfFamily_fixedSlice_eq_endpoint]
    have hPsiEq :
        Psi (Λ.linkEvaluateSide tau 0 hΛ U) =
          Psi (Λ.linkEvaluateSide tau 0 hΛ V) := by
      apply Psi.dependsOn_support
      intro e he
      have hec : e ∈ collar := by
        simpa [Psi, transverseStraightArmEndpoint, x, collar, tau,
          Path.advance_eq] using he
      let ep : P := ⟨e, hplus e hec⟩
      rw [Λ.linkEvaluateSide_apply_of_mem tau 0 hΛ U e (hplus e hec),
        Λ.linkEvaluateSide_apply_of_mem tau 0 hΛ V e (hplus e hec)]
      apply hUV ep
      simp [S, ep, hec]
    exact congrFun hPsiEq i
  obtain ⟨A, hA⟩ := transverseAxialEndpoint_nonzero hd eta x T hendpoint
  obtain ⟨i, hi⟩ : ∃ i : Fin n,
      transverseAxialEndpoint hd eta x T A i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hA (funext h)
  let U : LinkReflection.SideConfiguration G P := fun e => A e.1
  have hPsiA : Psi (Λ.linkEvaluateSide tau 0 hΛ U) =
      transverseAxialEndpoint hd eta x T A := by
    change transverseAxialEndpoint hd eta x T
        (Λ.linkEvaluateSide tau 0 hΛ U) = transverseAxialEndpoint hd eta x T A
    apply (transverseAxialEndpoint hd eta x T).dependsOn_support
    intro e he
    have hec : e ∈ collar := by simpa [collar] using he
    rw [Λ.linkEvaluateSide_apply_of_mem tau 0 hΛ U e (hplus e hec)]
  have hsliceNe :
      (⟨fun V : LinkReflection.SideConfiguration G P =>
          transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, V),
        (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i).continuous.comp
          (continuous_const.prodMk continuous_id)⟩ : C(P → G, ℂ)) ≠ 0 := by
    intro hzero
    have hzU := DFunLike.congr_fun hzero U
    simp only [ContinuousMap.zero_apply] at hzU
    change transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i (1, U) = 0 at hzU
    rw [transverseOneLinkHalfFamily_fixedSlice_eq_endpoint] at hzU
    exact hi (hPsiA ▸ hzU)
  have hS_collar (e : S) : e.1.1 ∈ collar := by
    have he := e.2
    change e.1 ∈ Finset.univ.filter (fun a => a.1 ∈ collar) at he
    exact (Finset.mem_filter.mp he).2
  let q : S → Λ.linkCrossPlaquettes tau 0 := fun e =>
    Classical.choose (hvisiblePrism e.1.1 (hS_collar e))
  have hq (e : S) :
      FiniteSpecification.linkCrossPositiveEdge tau (q e).1 = e.1.1 := by
    exact Classical.choose_spec (hvisiblePrism e.1.1 (hS_collar e))
  let D := Λ.linkWilsonDecomposition tau 0 hΛ sigma
  obtain ⟨r, w, hw⟩ := exists_taylorAmplitude_zero_ne_of_visible
    D hfaithful
    (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i) S
    (hsliceDep i) hsliceNe q (by
      intro V e
      unfold D FiniteSpecification.linkWilsonDecomposition
      change Λ.linkEvaluateSide tau 0 hΛ V
          (FiniteSpecification.linkCrossPositiveEdge tau (q e).1) = V e.1
      rw [hq e]
      exact Λ.linkEvaluateSide_apply_of_mem tau 0 hΛ V e.1.1 e.1.2)
  exact ⟨i, r, w, hw⟩

/-- Exact fixed-crossing-slice Gram-family factorization for the explicit
one-link screened observable. -/
theorem transverseOneLink_isGaugeFixedLinkFamilyNormSquare
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges) :
    Λ.IsGaugeFixedLinkFamilyPairing (Geometry.armAxis hd) 0 hΛ
      (transverseStraightArmObservable hd rho eta T z hz 0)
      (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz)
      (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz) := by
  let tau := Geometry.armAxis hd
  let q := straightPositiveHalfPath tau z 0
  let Psi := transverseStraightArmEndpoint hd eta T z 0
  let O := transverseStraightArmObservable hd rho eta T z hz 0
  let F := transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz
  have htarget : Path.advance (step z (.forward tau)) (.forward tau) 0 =
      step z (.forward tau) := by simp [Path.advance_eq]
  have hPsiCov : GaugeCovariantAt rho (step z (.forward tau)) Psi := by
    simpa [Psi, transverseStraightArmEndpoint, tau, htarget] using
      (transverseAxialEndpoint_covariant hd rho eta
        (step z (.forward tau)) T hT)
  have hPsi : Psi.SupportedInLinkPositiveHalf tau 0 := by
    simpa [Psi, transverseStraightArmEndpoint, tau, htarget, hz, step,
      SignedDirection.forward, SignedDirection.delta, unitVector] using
      (transverseAxialEndpoint_supportedInLinkPositiveHalf hd eta
        (step z (.forward tau)) T)
  have hq : Endpoint.Path.SupportedInLinkPositiveHalf tau 0 q := by
    exact straightPositiveHalfPath_supportedInLinkPositiveHalf tau 0 z hz 0
  obtain ⟨hin, hout⟩ := reflectedFullPath_sideSupport
    rho Psi tau 0 z hz q hPsi hq
  have hedynamic : crossingPositiveEdge z tau ∈ Λ.dynamicEdges := by
    apply hdyn
    simpa [O, transverseStraightArmObservable, Psi,
      transverseStraightArmEndpoint, q, tau] using
      (crossingPositiveEdge_mem_reflectedFullPath_support rho Psi tau z hz q)
  have hecross : crossingPositiveEdge z tau ∈ Λ.linkCrossingEdges tau 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hedynamic, rfl, hz⟩
  simpa [O, F, transverseOneLinkHalfFamily, Psi, q, tau] using
    (reflectedFullPath_isGaugeFixedLinkFamilyNormSquare
      Λ tau 0 hΛ rho Psi z hz q hPsiCov hdyn hecross hin hout)

/-- The finite one-link screened expectation is strictly positive whenever
one coordinate of its full endpoint Gram family is detected by a Taylor word
of the (independent) action representation `sigma`. -/
theorem transverseOneLink_finite_strict_of_detected
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    {beta : ℝ} (hbeta : 0 < beta)
    (hdetect : ∃ i,
      (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma).TaylorDetected
        beta (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i)) :
    0 < Complex.re
      (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
          (Λ.evaluate A)
        ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  let tau := Geometry.armAxis hd
  let O := transverseStraightArmObservable hd rho eta T z hz 0
  let F := transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz
  have hpair : Λ.IsGaugeFixedLinkFamilyPairing tau 0 hΛ O F F := by
    exact transverseOneLink_isGaugeFixedLinkFamilyNormSquare
      Λ hd hΛ rho eta T hT z hz hdyn
  exact YangMills.Gauge.LinkReflection.FiniteSpecification.linkCrossingFamilyReflectionStrictlyPositive_gibbsMeasure Λ
    tau 0 hΛ hclosed sigma hbeta O F hpair hdetect

/-- Explicit selected-word lower bound for the one-link screened expectation.
The amplitude contains an actual endpoint coordinate, and the right side is
the full screened observable, so this inequality keeps rather than cancels
the endpoint factor. -/
theorem transverseOneLink_finite_selectedWord_lowerBound
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    {beta : ℝ} (hbeta : 0 ≤ beta) (i : Fin n) {r : ℕ}
    (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
      (Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0) nsigma r) :
    (FiniteVolume.partitionFunction Λ sigma.wilsonPotential beta)⁻¹ *
        (Gauge.LinkReflection.WilsonActionDecomposition.taylorCoefficient
            (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma)
            beta r *
          ‖Gauge.LinkReflection.WilsonActionDecomposition.taylorAmplitude
            (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma) beta
              (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i) w‖ ^ 2) ≤
      Complex.re
        (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
            (Λ.evaluate A)
          ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  apply YangMills.Gauge.LinkReflection.FiniteSpecification.linkCrossingFamilyReflection_gibbsMeasure_selectedWord_lowerBound Λ
    (Geometry.armAxis hd) 0 hΛ hclosed sigma hbeta
    (transverseStraightArmObservable hd rho eta T z hz 0)
    (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz)
    (transverseOneLink_isGaugeFixedLinkFamilyNormSquare
      Λ hd hΛ rho eta T hT z hz hdyn) i w

/-- A word with nonzero independent-Haar amplitude gives strict positivity
throughout a punctured strong-coupling neighborhood.  This is the exact
finite-volume conclusion supplied by the roadmap strategy before Taylor-
coefficient stabilization is used to pass a positive coefficient to infinite
volume. -/
theorem eventually_transverseOneLink_finite_strict_of_amplitude_zero_ne
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    (hzero : ∃ (i : Fin n) (r : ℕ)
      (w : Gauge.LinkReflection.WilsonActionDecomposition.CrossWord
        (Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0) nsigma r),
      (Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma).taylorAmplitude
        0 (transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz i) w ≠ 0) :
    ∀ᶠ beta in 𝓝[>] (0 : ℝ),
      0 < Complex.re
        (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
            (Λ.evaluate A)
          ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  obtain ⟨i, r, w, hw⟩ := hzero
  let D := Λ.linkWilsonDecomposition (Geometry.armAxis hd) 0 hΛ sigma
  let F := transverseOneLinkHalfFamily Λ hd hΛ rho eta T z hz
  have hdet : ∀ᶠ beta in 𝓝 (0 : ℝ), D.TaylorDetected beta (F i) :=
    D.eventually_taylorDetected_of_amplitude_zero_ne (F i) w hw
  have hdet' : ∀ᶠ beta in 𝓝[>] (0 : ℝ), D.TaylorDetected beta (F i) :=
    Filter.Eventually.filter_mono inf_le_left hdet
  filter_upwards [hdet', self_mem_nhdsWithin] with beta hbeta hpositive
  exact transverseOneLink_finite_strict_of_detected Λ hd hΛ hclosed
    sigma rho eta T hT z hz hdyn hpositive ⟨i, hbeta⟩

/-- Concrete strict strong-coupling one-link lower bound.  Faithfulness of the
Wilson-action representation detects a nonzero transverse endpoint through
the cross-plane prisms, and the full endpoint Gram factor remains in the
selected-word estimate above. -/
theorem eventually_transverseOneLink_finite_strict
    [MeasureTheory.Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (hfaithful : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    (hendpoint : ∃ u : Fin m → G,
      T (fun j => Lie.axialMatrix eta (u j)) ≠ 0)
    (hcollarDyn : basedLoopSupport
      (transverseLoop (m := m) hd
        (step z (.forward (Geometry.armAxis hd)))) ⊆ Λ.dynamicEdges)
    (hvisiblePrism : ∀ e ∈ basedLoopSupport
      (transverseLoop (m := m) hd
        (step z (.forward (Geometry.armAxis hd)))),
      ∃ p : Λ.linkCrossPlaquettes (Geometry.armAxis hd) 0,
        FiniteSpecification.linkCrossPositiveEdge
          (Geometry.armAxis hd) p.1 = e) :
    ∀ᶠ beta in 𝓝[>] (0 : ℝ),
      0 < Complex.re
        (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
            (Λ.evaluate A)
          ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  apply eventually_transverseOneLink_finite_strict_of_amplitude_zero_ne
    Λ hd hΛ hclosed sigma rho eta T hT z hz hdyn
  exact transverseOneLink_exists_taylorAmplitude_zero_ne
    Λ hd hΛ sigma hfaithful rho eta T z hz hendpoint hcollarDyn hvisiblePrism

/-- Geometric form of the strict one-link theorem.  It is enough that every
plaquette perpendicular to the arm through the cutting plane is active; the
transverse-prism theorem then supplies the visibility hypothesis, explicitly
using the third lattice direction. -/
theorem eventually_transverseOneLink_finite_strict_of_crossPlaquettes_active
    [MeasureTheory.Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (Λ : FiniteSpecification d G) (hd : 3 ≤ d)
    (hΛ : Λ.LinkSymmetric (Geometry.armAxis hd) 0)
    (hclosed : Λ.PlaquetteClosed)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (hfaithful : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hdyn : (transverseStraightArmObservable hd rho eta T z hz 0).support ⊆
      Λ.dynamicEdges)
    (hendpoint : ∃ u : Fin m → G,
      T (fun j => Lie.axialMatrix eta (u j)) ≠ 0)
    (hcollarDyn : basedLoopSupport
      (transverseLoop (m := m) hd
        (step z (.forward (Geometry.armAxis hd)))) ⊆ Λ.dynamicEdges)
    (hactive : ∀ p : Plaquette d,
      p.base (Geometry.armAxis hd) = 0 →
      (p.first = Geometry.armAxis hd ∨
        p.second = Geometry.armAxis hd) →
      p ∈ Λ.activePlaquettes) :
    ∀ᶠ beta in 𝓝[>] (0 : ℝ),
      0 < Complex.re
        (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
            (Λ.evaluate A)
          ∂FiniteVolume.gibbsMeasure Λ sigma.wilsonPotential beta) := by
  apply eventually_transverseOneLink_finite_strict Λ hd hΛ hclosed sigma
    hfaithful rho eta T hT z hz hdyn hendpoint hcollarDyn
  apply transverseLoop_support_has_linkCrossPlaquette Λ hd
    (step z (.forward (Geometry.armAxis hd))) 0
  · simp [step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  · exact hactive

end

end YangMills.Gluelump.OneLink
