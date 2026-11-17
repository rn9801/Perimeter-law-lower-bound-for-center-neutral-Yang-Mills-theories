/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.SiteReflectionFamily
import GluelumpPerimeterLaw.Propagation.AntiDiagonalClosing
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixed
import GluelumpPerimeterLaw.Propagation.RectangleReflectionCore
import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryBoxes

/-!
# Coordinate-reflection inequalities for Wilson rectangles

This module supplies the integer-plane half of the standard rectangle
log-convexity argument.  An open cap with both endpoints on the reflection
plane is represented by all matrix coefficients of its holonomy.  Contracting
two such families closes the two caps into a Wilson loop.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory Gauge Lattice.Cubic Wilson StrongCoupling

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

variable [MeasurableSpace G]

variable [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Integer-plane reflection Cauchy--Schwarz for two open Wilson caps.  The
dimension factors cancel, leaving the normalized Wilson-loop expectations. -/
theorem centeredInfiniteVolume_siteCapsCauchySchwarz
    (eta : ℕ → Configuration d G)
    {nYM : ℕ} (rhoYM : ContinuousUnitaryRepData G nYM)
    (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rhoYM.wilsonPotential.bound)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p q : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (hp : ∀ e ∈ p.edgeSupport, k ≤ e.source τ)
    (hq : ∀ e ∈ q.edgeSupport, k ≤ e.source τ) :
    Complex.normSq (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k p hx hy).reverse.comp q) A
      ∂centeredInfiniteVolumeMeasure eta
        rhoYM.wilsonPotential beta hbeta) ≤
      Complex.re (∫ A, rho.wilsonLoop
          ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
        ∂centeredInfiniteVolumeMeasure eta
          rhoYM.wilsonPotential beta hbeta) *
      Complex.re (∫ A, rho.wilsonLoop
          ((siteReflectedPathFixed τ k q hx hy).reverse.comp q) A
        ∂centeredInfiniteVolumeMeasure eta
          rhoYM.wilsonPotential beta hbeta) := by
  let μ := centeredInfiniteVolumeMeasure eta
    rhoYM.wilsonPotential beta hbeta
  let F : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho p a
  let H : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho q a
  have hfamily := centeredInfiniteVolume_siteReflectionFamilyCauchySchwarz
    eta rhoYM beta hbeta τ k F H
    (fun a => holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k p hp a)
    (fun a => holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k q hq a)
  have hpair (u v : Lattice.Cubic.Path x y) :
      siteReflectionFamilyPairing μ τ k
          (fun a => holonomyMatrixFlattenedComponent rho u a)
          (fun a => holonomyMatrixFlattenedComponent rho v a) =
        (n : ℂ) * ∫ A, rho.wilsonLoop
          ((siteReflectedPathFixed τ k u hx hy).reverse.comp v) A ∂μ := by
    unfold siteReflectionFamilyPairing siteReflectionPairing
    rw [← integral_finsetSum]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        holonomyMatrix_siteReflectionFamilyProduct_apply
          rho τ k u v hx hy A
    · intro a _ha
      exact integrable_localObservable
        (centeredInfiniteVolumeProbability eta
          rhoYM.wilsonPotential beta hbeta)
        ((holonomyMatrixFlattenedComponent rho u a).siteReflectionProduct
          τ k (holonomyMatrixFlattenedComponent rho v a))
  change Complex.normSq (∫ A, rho.wilsonLoop
      ((siteReflectedPathFixed τ k p hx hy).reverse.comp q) A ∂μ) ≤ _
  rw [hpair p q] at hfamily
  have hdiag (u : Lattice.Cubic.Path x y) :
      (∑ a : Fin (n * n), Complex.re (siteReflectionPairing μ τ k
        (holonomyMatrixFlattenedComponent rho u a)
        (holonomyMatrixFlattenedComponent rho u a))) =
      (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k u hx hy).reverse.comp u) A ∂μ) := by
    have h := congrArg Complex.re (hpair u u)
    unfold siteReflectionFamilyPairing at h
    simp only [Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at h
    simpa using h
  dsimp [F, H] at hfamily
  rw [hdiag p, hdiag q] at hfamily
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  simp only [Complex.normSq_mul, Complex.normSq_natCast,
    Complex.natCast_re] at hfamily
  nlinarith [sq_pos_of_pos hn]

/-- A site-reflection self-closure has nonnegative real Wilson expectation. -/
theorem centeredInfiniteVolume_siteCapsNonneg
    (eta : ℕ → Configuration d G)
    {nYM : ℕ} (rhoYM : ContinuousUnitaryRepData G nYM)
    (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rhoYM.wilsonPotential.bound)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (hp : ∀ e ∈ p.edgeSupport, k ≤ e.source τ) :
    0 ≤ Complex.re (∫ A, rho.wilsonLoop
      ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
      ∂centeredInfiniteVolumeMeasure eta
        rhoYM.wilsonPotential beta hbeta) := by
  let μ := centeredInfiniteVolumeMeasure eta
    rhoYM.wilsonPotential beta hbeta
  let F : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho p a
  have hfamily := centeredInfiniteVolume_siteReflectionFamilyPositive
    eta rhoYM beta hbeta τ k F
    (fun a => holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k p hp a)
  have hpair : siteReflectionFamilyPairing μ τ k F F =
      (n : ℂ) * ∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A ∂μ := by
    unfold F siteReflectionFamilyPairing siteReflectionPairing
    rw [← integral_finsetSum]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        holonomyMatrix_siteReflectionFamilyProduct_apply
          rho τ k p p hx hy A
    · intro a _ha
      exact integrable_localObservable
        (centeredInfiniteVolumeProbability eta
          rhoYM.wilsonPotential beta hbeta)
        ((holonomyMatrixFlattenedComponent rho p a).siteReflectionProduct
          τ k (holonomyMatrixFlattenedComponent rho p a))
  rw [hpair] at hfamily
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hfamily
  nlinarith [hfamily.2]

/-! ## Half-integer planes -/

/-- A matrix coefficient of the reflected cap, oriented from the lower to the
upper negative-side crossing site. -/
def reflectedCapMatrixComponent
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (a : Fin (n * n)) : LocalObservable d G :=
  holonomyMatrixFlattenedComponent rho
    (reflectedIncomingPath τ k z hz p).reverse a

/-- Restricting a reflected negative cap to one side is the same matrix
coefficient as evaluating the original positive cap on that side. -/
theorem linkRestrictNegative_reflectedCapMatrix_eq_positive
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (z : Site d) (hz : z τ = k) {y : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (a : Fin (n * n))
    (hin : (reflectedCapMatrixComponent rho τ k z hz p a).conj.linkTheta
      τ k |>.SupportedInLinkPositiveHalf τ k)
    (U : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) :
    linkRestrictNegativeObservable Λ τ k hΛ
        (reflectedCapMatrixComponent rho τ k z hz p a) (1, U) =
      holonomyMatrixFlattenedComponent rho p a
        (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, U)))) := by
  let Win : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (U, 1))
  let Wout : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (1, U))
  have hrestrict := linkRestrictNegativeObservable_apply_assemble_fixed
    Λ τ k hΛ (reflectedCapMatrixComponent rho τ k z hz p a)
      hin U 1
  have hreflect := Λ.linkAssemble_reflect τ k hΛ Wout
  have hinvOne : LinkReflection.invertCrossing
      (1 : LinkReflection.CrossingConfiguration G
        (Λ.linkCrossingEdges τ k)) = 1 := by
    funext e
    simp [LinkReflection.invertCrossing]
  have hWin : Λ.evaluate (Λ.linkAssemble τ k hΛ Win) =
      linkReflectConfiguration τ k
        (Λ.evaluate (Λ.linkAssemble τ k hΛ Wout)) := by
    simpa [Win, Wout, LinkReflection.reflect, hinvOne] using hreflect
  rw [← hrestrict]
  change reflectedCapMatrixComponent rho τ k z hz p a
      (Λ.evaluate (Λ.linkAssemble τ k hΛ Win)) = _
  rw [hWin]
  simp only [reflectedCapMatrixComponent,
    holonomyMatrixFlattenedComponent_apply, holonomy_reverse,
    holonomy_reflectedIncomingPath_linkReflectConfiguration, inv_inv]
  rfl

/-- Two positive caps give the exact mixed finite Gram pairing after both
crossing links are gauge-fixed. -/
theorem linkClosedCaps_isGaugeFixedLinkFamilyPairing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (z w : Site d) (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ))
    (hdyn : (linkClosedCapsObservable rho τ k z w hz hw p q hy hu).support ⊆
      Λ.dynamicEdges)
    (hbottom : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ k)
    (htop : topCrossingPositiveEdge w τ ∈ Λ.linkCrossingEdges τ k)
    (hinp : ∀ a, ((reflectedCapMatrixComponent rho τ k z hz p a).conj
      |>.linkTheta τ k).SupportedInLinkPositiveHalf τ k)
    (hinq : ∀ a, ((reflectedCapMatrixComponent rho τ k z hz q a).conj
      |>.linkTheta τ k).SupportedInLinkPositiveHalf τ k)
    (hqp : ∀ e ∈ q.edgeSupport, k < e.target τ) :
    Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ
      (linkClosedCapsObservable rho τ k z w hz hw p q hy hu)
      (fun a => linkRestrictNegativeObservable Λ τ k hΛ
        (reflectedCapMatrixComponent rho τ k z hz p a))
      (fun a => linkRestrictNegativeObservable Λ τ k hΛ
        (reflectedCapMatrixComponent rho τ k z hz q a)) := by
  apply Λ.isGaugeFixedLinkFamilyPairing_of_gaugeInvariant τ k hΛ
    (linkClosedCapsObservable rho τ k z w hz hw p q hy hu)
    (fun a => linkRestrictNegativeObservable Λ τ k hΛ
      (reflectedCapMatrixComponent rho τ k z hz p a))
    (fun a => linkRestrictNegativeObservable Λ τ k hΛ
      (reflectedCapMatrixComponent rho τ k z hz q a))
  · intro gauge A
    rw [linkClosedCapsObservable_apply, linkClosedCapsObservable_apply]
    exact congrArg ((n : ℂ) * ·)
      (rho.wilsonLoop_gaugeInvariant
        (linkClosedCapsPath τ k z w hz hw p q hy hu) gauge A)
  · exact hdyn
  · intro Uminus Uplus
    let A := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))
    let B := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, Uplus)))
    have hbottomA : A (crossingPositiveEdge z τ) = 1 :=
      Λ.linkCrossingEdge_value_fixed τ k hΛ (Uminus, Uplus)
        (crossingPositiveEdge z τ) hbottom
    have htopA : A (topCrossingPositiveEdge w τ) = 1 :=
      Λ.linkCrossingEdge_value_fixed τ k hΛ (Uminus, Uplus)
        (topCrossingPositiveEdge w τ) htop
    have hhol := holonomy_linkClosedCapsPath_of_crossings_one
      τ k z w hz hw p q hy hu A hbottomA htopA
    rw [linkClosedCapsObservable_apply,
      ContinuousUnitaryRepData.wilsonLoop_apply, hhol]
    have hscale (g : G) :
        (n : ℂ) * rho.normalizedCharacter g = rho.character g := by
      unfold ContinuousUnitaryRepData.normalizedCharacter
      have hn : (n : ℂ) ≠ 0 := by exact_mod_cast rho.dimension_pos.ne'
      field_simp
    rw [hscale]
    have hmatrix := sum_star_representationMatrix_mul_eq_character rho
      (holonomy A (reflectedIncomingPath τ k z hz p).reverse)
      (holonomy A q)
    simp only [holonomy_reverse, inv_inv] at hmatrix
    rw [← hmatrix]
    apply Finset.sum_congr rfl
    intro a _ha
    have hleft := linkRestrictNegativeObservable_apply_assemble_fixed
      Λ τ k hΛ (reflectedCapMatrixComponent rho τ k z hz p a)
      (hinp a) Uminus Uplus
    have hqSupport :
        (holonomyMatrixFlattenedComponent rho q a).SupportedInLinkPositiveHalf
          τ k := by
      intro e he
      exact hqp e he
    have houtA := Λ.linkRestrictObservable_apply_assemble τ k hΛ
      (holonomyMatrixFlattenedComponent rho q a) hqSupport
      (1, (Uminus, Uplus))
    have houtB := Λ.linkRestrictObservable_apply_assemble τ k hΛ
      (holonomyMatrixFlattenedComponent rho q a) hqSupport
      (1, (1, Uplus))
    have hright := linkRestrictNegative_reflectedCapMatrix_eq_positive
      Λ τ k hΛ rho z hz q a (hinq a) Uplus
    have hleft' :
        (rho.ρ (holonomy A (reflectedIncomingPath τ k z hz p))⁻¹ :
          Matrix (Fin n) (Fin n) ℂ)
            (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 =
          linkRestrictNegativeObservable Λ τ k hΛ
            (reflectedCapMatrixComponent rho τ k z hz p a) (1, Uminus) := by
      simpa [reflectedCapMatrixComponent, holonomy_reverse] using hleft
    rw [hleft']
    have houtAB : holonomyMatrixFlattenedComponent rho q a A =
        holonomyMatrixFlattenedComponent rho q a B := by
      rw [houtA, houtB]
    have houtAB' :
        (rho.ρ (holonomy A q) : Matrix (Fin n) (Fin n) ℂ)
            (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 =
          (rho.ρ (holonomy B q) : Matrix (Fin n) (Fin n) ℂ)
            (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 := by
      simpa using houtAB
    rw [houtAB']
    exact congrArg (star
      (linkRestrictNegativeObservable Λ τ k hΛ
        (reflectedCapMatrixComponent rho τ k z hz p a) (1, Uminus)) * ·)
      hright.symm

/-- The lower crossing edge is recorded in every closed-cap observable. -/
theorem crossingPositiveEdge_mem_linkClosedCapsObservable_support
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ)) :
    crossingPositiveEdge z τ ∈
      (linkClosedCapsObservable rho τ k z w hz hw p q hy hu).support := by
  change crossingPositiveEdge z τ ∈
    (linkClosedCapsPath τ k z w hz hw p q hy hu).edgeSupport
  unfold linkClosedCapsPath
  rw [Path.edgeSupport_comp, Path.edgeSupport_castTarget,
    Path.edgeSupport_castSource]
  apply Finset.mem_union_left
  unfold reflectedMixedFullPath
  rw [Path.edgeSupport_comp]
  apply Finset.mem_union_right
  unfold crossingThenPath
  rw [Path.edgeSupport_comp]
  apply Finset.mem_union_left
  change crossingPositiveEdge z τ ∈
    ({crossingPositiveEdge z τ} : Finset (PositiveEdge d))
  simp

/-- The upper crossing edge is also recorded in every closed-cap observable. -/
theorem topCrossingPositiveEdge_mem_linkClosedCapsObservable_support
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ)) :
    topCrossingPositiveEdge w τ ∈
      (linkClosedCapsObservable rho τ k z w hz hw p q hy hu).support := by
  change topCrossingPositiveEdge w τ ∈
    (linkClosedCapsPath τ k z w hz hw p q hy hu).edgeSupport
  unfold linkClosedCapsPath
  rw [Path.edgeSupport_comp]
  apply Finset.mem_union_right
  change topCrossingPositiveEdge w τ ∈
    insert (Quiver.reverse (edgeFrom w (.forward τ))).1.positive ∅
  rw [show (Quiver.reverse (edgeFrom w (.forward τ))).1.positive =
      (edgeFrom w (.forward τ)).1.positive by
        exact SignedEdge.positive_reverse (edgeFrom w (.forward τ)).1]
  change topCrossingPositiveEdge w τ ∈
    insert (topCrossingPositiveEdge w τ) ∅
  simp

/-- Positive cap geometry puts every reflected transport coefficient in the
positive link algebra after conjugate reflection. -/
theorem reflectedCapMatrix_conj_linkTheta_supportedInLinkPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (hp : ∀ e ∈ p.edgeSupport, k < e.target τ)
    (a : Fin (n * n)) :
    LocalObservable.SupportedInLinkPositiveHalf τ k
      ((reflectedCapMatrixComponent rho τ k z hz p a).conj.linkTheta τ k) := by
  change ∀ e ∈ ((Path.edgeSupport
      (reflectedIncomingPath τ k z hz p).reverse).image
        (PositiveEdge.linkReflect τ k)), k < PositiveEdge.target e τ
  rw [edgeSupport_reverse, reflectedIncomingPath_support_image_linkReflect]
  exact hp

/-- The two-crossing gauge-fixed construction persists along the ordinary
free-boundary exhaustion and supplies the missing half-integer cap
Cauchy--Schwarz certificate. -/
theorem eventuallyLinkCrossingFamilyCauchySchwarz_linkClosedCaps
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (z w : Site d) (hz : z τ = 0) (hw : w τ = 0)
    (p q : Lattice.Cubic.Path
      (step z (.forward τ)) (step w (.forward τ)))
    (hp : ∀ e ∈ p.edgeSupport, 0 < e.target τ)
    (hq : ∀ e ∈ q.edgeSupport, 0 < e.target τ) :
    EventuallyLinkCrossingFamilyCauchySchwarz (ι := Fin (n * n)) τ
      (linkClosedCapsObservable rho τ 0 z w hz hw p q rfl rfl)
      (linkClosedCapsObservable rho τ 0 z w hz hw p p rfl rfl)
      (linkClosedCapsObservable rho τ 0 z w hz hw q q rfl rfl) := by
  let OFH := linkClosedCapsObservable rho τ 0 z w hz hw p q rfl rfl
  let OFF := linkClosedCapsObservable rho τ 0 z w hz hw p p rfl rfl
  let OHH := linkClosedCapsObservable rho τ 0 z w hz hw q q rfl rfl
  have hinp := fun a =>
    reflectedCapMatrix_conj_linkTheta_supportedInLinkPositiveHalf
      rho τ 0 z hz p hp a
  have hinq := fun a =>
    reflectedCapMatrix_conj_linkTheta_supportedInLinkPositiveHalf
      rho τ 0 z hz q hq a
  filter_upwards
      [support_subset_freeBoundarySpecification_eventually τ OFH,
       support_subset_freeBoundarySpecification_eventually τ OFF,
       support_subset_freeBoundarySpecification_eventually τ OHH]
      with N hFHdyn hFFdyn hHHdyn
  let Λ := freeBoundarySpecification G d N τ
  have hbottom : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hFHdyn (crossingPositiveEdge_mem_linkClosedCapsObservable_support
      rho τ 0 z w hz hw p q rfl rfl), rfl, hz⟩
  have htop : topCrossingPositiveEdge w τ ∈ Λ.linkCrossingEdges τ 0 := by
    rw [FiniteSpecification.linkCrossingEdges, Finset.mem_filter]
    exact ⟨hFHdyn (topCrossingPositiveEdge_mem_linkClosedCapsObservable_support
      rho τ 0 z w hz hw p q rfl rfl), rfl, hw⟩
  let F := fun a => linkRestrictNegativeObservable Λ τ 0
    (freeBoundarySpecification_linkSymmetric N τ)
    (reflectedCapMatrixComponent rho τ 0 z hz p a)
  let H := fun a => linkRestrictNegativeObservable Λ τ 0
    (freeBoundarySpecification_linkSymmetric N τ)
    (reflectedCapMatrixComponent rho τ 0 z hz q a)
  refine ⟨F, H, ?_, ?_, ?_⟩
  · exact linkClosedCaps_isGaugeFixedLinkFamilyPairing
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho z w hz hw p q rfl rfl hFHdyn hbottom htop hinp hinq hq
  · exact linkClosedCaps_isGaugeFixedLinkFamilyPairing
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho z w hz hw p p rfl rfl hFFdyn hbottom htop hinp hinp hp
  · exact linkClosedCaps_isGaugeFixedLinkFamilyPairing
      Λ τ 0 (freeBoundarySpecification_linkSymmetric N τ)
      rho z w hz hw q q rfl rfl hHHdyn hbottom htop hinq hinq hq

/-- A link-reflection self-closure has nonnegative real Wilson expectation;
the gauge-fixed crossing construction is used before taking the limit. -/
theorem centeredInfiniteVolume_linkCapsNonneg
    (eta : ℕ → Configuration d G)
    {nYM : ℕ} (rhoYM : ContinuousUnitaryRepData G nYM)
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rhoYM.wilsonPotential.bound)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (z w : Site d) (hz : z τ = 0) (hw : w τ = 0)
    (p : Lattice.Cubic.Path
      (step z (.forward τ)) (step w (.forward τ)))
    (hp : ∀ e ∈ p.edgeSupport, 0 < e.target τ) :
    0 ≤ Complex.re (∫ A, rho.wilsonLoop
      (linkClosedCapsPath τ 0 z w hz hw p p rfl rfl) A
      ∂centeredInfiniteVolumeMeasure eta
        rhoYM.wilsonPotential beta hbeta) := by
  let O := linkClosedCapsObservable rho τ 0 z w hz hw p p rfl rfl
  have hpair : EventuallyLinkCrossingFamilyNormSquare
      (ι := Fin (n * n)) τ O := by
    have hcs := eventuallyLinkCrossingFamilyCauchySchwarz_linkClosedCaps
      rho τ z w hz hw p p hp hp
    filter_upwards [hcs] with N hN
    obtain ⟨F, H, hFH, hFF, hHH⟩ := hN
    exact ⟨F, hFF⟩
  have hpos := centeredInfiniteVolume_linkCrossingFamilyReflectionPositive_half
    eta rhoYM beta hbeta0 hbeta τ O hpair
  dsimp [O, linkClosedCapsObservable] at hpos
  simp_rw [integral_const_mul] at hpos
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hpos
  nlinarith [hpos.2]

/-- Half-integer coordinate reflection gives Cauchy--Schwarz for closed
Wilson caps of odd total width.  Both crossing links are gauge-fixed in the
finite approximants, and the representation-dimension factors cancel after
passing to infinite volume. -/
theorem centeredInfiniteVolume_linkCapsCauchySchwarz
    (eta : ℕ → Configuration d G)
    {nYM : ℕ} (rhoYM : ContinuousUnitaryRepData G nYM)
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rhoYM.wilsonPotential.bound)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (z w : Site d) (hz : z τ = 0) (hw : w τ = 0)
    (p q : Lattice.Cubic.Path
      (step z (.forward τ)) (step w (.forward τ)))
    (hp : ∀ e ∈ p.edgeSupport, 0 < e.target τ)
    (hq : ∀ e ∈ q.edgeSupport, 0 < e.target τ) :
    Complex.normSq (∫ A, rho.wilsonLoop
        (linkClosedCapsPath τ 0 z w hz hw p q rfl rfl) A
      ∂centeredInfiniteVolumeMeasure eta
        rhoYM.wilsonPotential beta hbeta) ≤
      Complex.re (∫ A, rho.wilsonLoop
          (linkClosedCapsPath τ 0 z w hz hw p p rfl rfl) A
        ∂centeredInfiniteVolumeMeasure eta
          rhoYM.wilsonPotential beta hbeta) *
      Complex.re (∫ A, rho.wilsonLoop
          (linkClosedCapsPath τ 0 z w hz hw q q rfl rfl) A
        ∂centeredInfiniteVolumeMeasure eta
          rhoYM.wilsonPotential beta hbeta) := by
  let μ := centeredInfiniteVolumeMeasure eta
    rhoYM.wilsonPotential beta hbeta
  let OFH := linkClosedCapsObservable rho τ 0 z w hz hw p q rfl rfl
  let OFF := linkClosedCapsObservable rho τ 0 z w hz hw p p rfl rfl
  let OHH := linkClosedCapsObservable rho τ 0 z w hz hw q q rfl rfl
  have hcs := centeredInfiniteVolume_linkCrossingFamilyCauchySchwarz_half
    (ι := Fin (n * n)) eta rhoYM beta hbeta0 hbeta τ OFH OFF OHH
    (eventuallyLinkCrossingFamilyCauchySchwarz_linkClosedCaps
      rho τ z w hz hw p q hp hq)
  change Complex.normSq (∫ A, rho.wilsonLoop
      (linkClosedCapsPath τ 0 z w hz hw p q rfl rfl) A ∂μ) ≤ _
  dsimp [OFH, OFF, OHH] at hcs
  simp_rw [integral_const_mul] at hcs
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  simp only [Complex.normSq_mul, Complex.normSq_natCast,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hcs
  nlinarith [sq_pos_of_pos hn]

end

end YangMills.Gluelump.Propagation
