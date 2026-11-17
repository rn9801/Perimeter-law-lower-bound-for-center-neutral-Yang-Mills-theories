/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.CenterNeutralLowerBound
import GluelumpPerimeterLaw.OneLink.ExhaustionStrictPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryInfiniteVolume
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryBoxes

/-!
# Direct one-link positivity in a free-boundary thermodynamic limit

The ordinary free-boundary boxes eventually satisfy the explicit geometric
admissibility conditions used by the all-positive-coupling direct one-link
estimate.  Consequently the box-independent lower constant supplied by
center neutrality passes to every probability measure satisfying the
free-boundary local-limit hypothesis.  The same finite Gram identity makes
the expectation real, and reality also passes to the limit.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint
open RepresentationTheory Representation
open StrongCoupling Filter Set

noncomputable section

universe u

variable {d n r m : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

omit [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)] in
/-- Sufficiently large ordinary free-boundary boxes satisfy all geometric
and support assumptions used by the direct conjugation-span one-link bound. -/
theorem eventually_conjSpanOneLinkAdmissible_freeBoundarySpecification
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) :
    ∀ᶠ boxRadius in atTop,
      ConjSpanOneLinkAdmissible
        (freeBoundarySpecification G d boxRadius (Geometry.armAxis hd))
        hd sigma rho T z hz := by
  let tau := Geometry.armAxis hd
  let y := step z (.forward tau)
  let collar := combEndpointCollar (m := m) hd y
  let O := conjSpanReflectedOneLinkObservable hd sigma rho T z hz
  classical
  let completedCollar := collar ∪
    (collar.biUnion incidentPlaquettes).biUnion fun p => p.boundary.edgeSupport
  obtain ⟨collarRadius, hcollar⟩ :=
    finiteSupport_subset_linkSymmetricBox tau completedCollar
  obtain ⟨observableRadius, hobservable⟩ :=
    finiteSupport_subset_linkSymmetricBox tau O.support
  refine Filter.eventually_atTop.2
    ⟨max collarRadius observableRadius, fun boxRadius hRadius => ?_⟩
  let Lambda := freeBoundarySpecification G d boxRadius tau
  have hcompletedBox : completedCollar ⊆
      (linkSymmetricBox d boxRadius tau).positiveEdges :=
    hcollar.trans (linkSymmetricBox_positiveEdges_mono
      ((Nat.le_max_left collarRadius observableRadius).trans hRadius) tau)
  have hcollarBox : collar ⊆
      (linkSymmetricBox d boxRadius tau).positiveEdges := by
    intro e he
    exact hcompletedBox (Finset.mem_union_left _ he)
  have hobservableBox : O.support ⊆
      (linkSymmetricBox d boxRadius tau).positiveEdges :=
    hobservable.trans (linkSymmetricBox_positiveEdges_mono
      ((Nat.le_max_right collarRadius observableRadius).trans hRadius) tau)
  have hy : y tau = 1 := by
    simp [y, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hcollarPositive : collar ⊆ Lambda.linkPositiveEdges tau 0 := by
    intro e he
    rw [FiniteSpecification.linkPositiveEdges, Finset.mem_filter]
    refine ⟨hcollarBox he, ?_⟩
    have hplane := basedLoopSupport_combLoops_armPlane hd y e he
    rw [hplane.1, hy]
    norm_num
  have hvisible : ∀ e ∈ collar,
      ∃ p : Lambda.linkCrossPlaquettes tau 0,
        FiniteSpecification.linkCrossPositiveEdge tau p.1 = e := by
    intro e he
    obtain ⟨p, hpbase, hpperp, hpedge, hpboundary⟩ :=
      transverseLoop_support_has_prismPlaquette hd y e he
    have hpbase' : p.base tau = 0 := by
      change p.base (Geometry.armAxis hd) = 0
      rw [hpbase]
      change y tau - 1 = 0
      rw [hy]
      norm_num
    have hpactive : p ∈ Lambda.activePlaquettes := by
      apply (mem_freeBoundaryActivePlaquettes_iff boxRadius tau p).mpr
      intro f hf
      apply hcompletedBox
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_biUnion.mpr
          ⟨e, he, mem_incidentPlaquettes_of_mem_boundary e p hpboundary⟩, hf⟩)
    exact ⟨⟨p, Finset.mem_filter.mpr ⟨hpactive, hpbase', hpperp⟩⟩, hpedge⟩
  exact ⟨freeBoundarySpecification_linkSymmetric boxRadius tau,
    freeBoundarySpecification_plaquetteClosed boxRadius tau,
    hcollarPositive, hvisible, hobservableBox⟩

omit [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)] in
/-- In every admissible finite box the direct reflected one-link expectation
is real.  This is the zero-imaginary-part half of its exact Gram-family
factorization. -/
theorem ConjSpanOneLinkAdmissible.gibbsExpectation_im_eq_zero
    (Lambda : FiniteSpecification d G) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hLambda : ConjSpanOneLinkAdmissible Lambda hd sigma rho T z hz)
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    Complex.im (∫ A,
      conjSpanReflectedOneLinkObservable hd sigma rho T z hz
        (Lambda.evaluate A)
      ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) = 0 := by
  let tau := Geometry.armAxis hd
  let y := step z (.forward tau)
  have hy : y tau = 1 := by
    simp [y, tau, step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hz]
  have hsupport : (conjSpanPhi hd sigma rho T y).SupportedInLinkPositiveHalf
      tau 0 := by
    have h := conjSpanPhi_supportedInLinkPositiveHalf hd sigma rho T y
    simpa only [tau, hy, sub_self] using h
  have hcertificate := reflectedEndpointOneLink_isGaugeFixedLinkFamilyNormSquare
    Lambda tau hLambda.linkSymmetric rho (conjSpanPhi hd sigma rho T y) z hz
      (conjSpanPhi_gauge_covariant hd sigma rho T y) hsupport
      hLambda.dynamicSupport
  exact (Lambda.linkCrossingFamilyReflectionPositive_gibbsMeasure
    tau 0 hLambda.linkSymmetric hLambda.plaquetteClosed sigma hbeta
    (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)
    (reflectedEndpointOneLinkHalfFamily Lambda tau hLambda.linkSymmetric rho
      (conjSpanPhi hd sigma rho T y) z hz) hcertificate).1

/-- The explicit finite-volume one-link constant passes to every common
local limit, for screening data fixed before the coupling is chosen. -/
theorem conjSpanOneLinkLowerConstant_le_freeBoundaryLimit
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (hT : T ≠ 0)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 < beta)
    {mu : ProbabilityMeasure (Configuration d G)}
    (hmu : IsTranslationInvariantFreeBoundaryLimit
      sigma.wilsonPotential beta mu) :
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT
        (step z (.forward (Geometry.armAxis hd))) ≤
      Complex.re (localExpectation mu
        (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)) ∧
      Complex.im (localExpectation mu
        (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)) = 0 := by
  let q := conjSpanOneLinkLowerConstant beta hd sigma rho T hT
    (step z (.forward (Geometry.armAxis hd)))
  let tau := Geometry.armAxis hd
  let O := conjSpanReflectedOneLinkObservable hd sigma rho T z hz
  have hadmissible :=
    eventually_conjSpanOneLinkAdmissible_freeBoundarySpecification
      hd sigma rho T z hz
  have hfiniteRe : ∀ᶠ boxRadius in atTop,
      q ≤ Complex.re (localExpectation
        (freeBoundaryGibbsSequence sigma.wilsonPotential beta tau boxRadius)
        O) := by
    filter_upwards [hadmissible] with boxRadius hbox
    simpa only [O, tau, freeBoundaryGibbsSequence,
      localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure] using
      ConjSpanOneLinkAdmissible.lowerBound
        (freeBoundarySpecification G d boxRadius tau) hd sigma rho T hT
          z hz hbox hbeta
  have hfiniteIm : ∀ᶠ boxRadius in atTop,
      Complex.im (localExpectation
        (freeBoundaryGibbsSequence sigma.wilsonPotential beta tau boxRadius)
        O) = 0 := by
    filter_upwards [hadmissible] with boxRadius hbox
    simpa only [O, tau, freeBoundaryGibbsSequence,
      localExpectation_fullGibbsProbability,
      complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure] using
      (ConjSpanOneLinkAdmissible.gibbsExpectation_im_eq_zero
        (freeBoundarySpecification G d boxRadius tau) hd sigma rho T z hz
          hbox hbeta.le)
  have hconv := hmu.localLimit tau O
  have hre : Tendsto (fun boxRadius => Complex.re (localExpectation
      (freeBoundaryGibbsSequence sigma.wilsonPotential beta tau boxRadius)
        O)) atTop
      (nhds (Complex.re (localExpectation mu O))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hconv
  have him : Tendsto (fun boxRadius => Complex.im (localExpectation
      (freeBoundaryGibbsSequence sigma.wilsonPotential beta tau boxRadius)
        O)) atTop
      (nhds (Complex.im (localExpectation mu O))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hconv
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun boxRadius => Complex.im (localExpectation
      (freeBoundaryGibbsSequence sigma.wilsonPotential beta tau boxRadius)
        O)) =ᶠ[atTop] fun _ => (0 : ℝ) := hfiniteIm
  exact ⟨isClosed_Ici.mem_of_tendsto hre hfiniteRe,
    tendsto_nhds_unique him (himZero.congr' heventIm.symm)⟩

/-- Center neutrality supplies one tensor degree, one nonzero screening map,
and one strictly positive real lower bound which work for every
translation-invariant ordinary free-boundary thermodynamic limit.  In
particular, the witnesses are chosen before the limiting probability. -/
theorem centerNeutral_exists_uniform_conjSpanOneLink_freeBoundaryLimit_lowerBound
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G r)
    (hcenter : CenterNeutral (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
        (tensorPower (conjSpanRep sigma) m) (asRepresentation rho),
      T ≠ 0 ∧ ∃ q : ℝ, 0 < q ∧
        ∀ mu : ProbabilityMeasure (Configuration d G),
          IsTranslationInvariantFreeBoundaryLimit
              sigma.wilsonPotential beta mu →
            q ≤ Complex.re (localExpectation mu
              (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)) ∧
            Complex.im (localExpectation mu
              (conjSpanReflectedOneLinkObservable hd sigma rho T z hz)) = 0 := by
  obtain ⟨m, T, hT⟩ :=
    centerNeutral_exists_conjSpanIntertwiner sigma hsigma rho hcenter
  refine ⟨m, T, hT,
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT
      (step z (.forward (Geometry.armAxis hd))),
    conjSpanOneLinkLowerConstant_pos hbeta hd sigma rho T hT _, ?_⟩
  intro mu hmu
  exact conjSpanOneLinkLowerConstant_le_freeBoundaryLimit
    hd sigma rho T hT z hz hbeta hmu

/-- Translation invariance moves the same uniform real lower bound to every
lattice translate of the canonical one-link seed. -/
theorem centerNeutral_exists_uniform_translatedConjSpanOneLink_freeBoundaryLimit_lowerBound
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G r)
    (hcenter : CenterNeutral (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
        (tensorPower (conjSpanRep sigma) m) (asRepresentation rho),
      T ≠ 0 ∧ ∃ q : ℝ, 0 < q ∧
        ∀ mu : ProbabilityMeasure (Configuration d G),
          IsTranslationInvariantFreeBoundaryLimit
              sigma.wilsonPotential beta mu →
            ∀ v : Site d,
              q ≤ Complex.re (localExpectation mu
                (LocalObservable.translatePullback v
                  (conjSpanReflectedOneLinkObservable hd sigma rho T z hz))) ∧
              Complex.im (localExpectation mu
                (LocalObservable.translatePullback v
                  (conjSpanReflectedOneLinkObservable hd sigma rho T z hz))) = 0 := by
  obtain ⟨m, T, hT, q, hq, hlimit⟩ :=
    centerNeutral_exists_uniform_conjSpanOneLink_freeBoundaryLimit_lowerBound
      hd sigma hsigma rho hcenter z hz hbeta
  refine ⟨m, T, hT, q, hq, fun mu hmu v => ?_⟩
  have hcanonical := hlimit mu hmu
  rw [hmu.localExpectation_translatePullback]
  exact hcanonical

end

end YangMills.Gluelump.OneLink
