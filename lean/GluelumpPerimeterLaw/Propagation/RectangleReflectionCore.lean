/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState
import GluelumpPerimeterLaw.Propagation.AntiDiagonalClosingCore
import GluelumpPerimeterLaw.Propagation.ReflectedLineCore
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixedCore
import GluelumpPerimeterLaw.Upstream.Wilson.Loop

/-!
# Measure-independent reflected Wilson caps

This file contains the pointwise path and holonomy identities for site- and
link-reflected Wilson caps.  It also derives the site-cap finite-family
positivity and Cauchy--Schwarz statements from the neutral
`ReflectionPositiveState` interface.  Gauge-fixed crossing-link input is
deliberately left to a separate adapter because its half-observables depend on
the finite box.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory Gauge Lattice.Cubic Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Cast a site-reflected path back to endpoints fixed by the reflecting
integer plane. -/
def siteReflectedPathFixed
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y) :
    Lattice.Cubic.Path x y :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource (p.siteReflect τ k) hx) hy

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem holonomy_siteReflectedPathFixed
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (A : Configuration d G) :
    holonomy A (siteReflectedPathFixed τ k p hx hy) =
      holonomy (siteReflectConfiguration τ k A) p := by
  unfold siteReflectedPathFixed
  rw [holonomy_castTarget, holonomy_castSource,
    holonomy_siteReflectConfiguration]

/-- The site-reflection contraction of two transport-matrix families is the
unnormalized character of the loop formed by the two reflected caps. -/
theorem holonomyMatrix_siteReflectionFamilyProduct_apply
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p q : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (A : Configuration d G) :
    (∑ a : Fin (n * n),
      (holonomyMatrixFlattenedComponent rho p a).siteReflectionProduct
        τ k (holonomyMatrixFlattenedComponent rho q a) A) =
      (n : ℂ) * rho.wilsonLoop
        ((siteReflectedPathFixed τ k p hx hy).reverse.comp q) A := by
  simp only [LocalObservable.siteReflectionProduct_apply,
    holonomyMatrixFlattenedComponent_apply]
  rw [sum_star_representationMatrix_mul_eq_character]
  simp only [ContinuousUnitaryRepData.wilsonLoop_apply, holonomy_comp,
    holonomy_reverse, holonomy_siteReflectedPathFixed]
  unfold ContinuousUnitaryRepData.normalizedCharacter
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast rho.dimension_pos.ne'
  field_simp

variable [MeasurableSpace G]

/-- Edge support of a matrix coefficient is positive whenever the underlying
cap is positive. -/
theorem holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p : Lattice.Cubic.Path x y)
    (hp : ∀ e ∈ p.edgeSupport, k ≤ e.source τ)
    (a : Fin (n * n)) :
    (holonomyMatrixFlattenedComponent rho p a).SupportedInSitePositiveHalf
      τ k := by
  intro e he
  exact hp e he

variable [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

omit [Group G] [IsTopologicalGroup G] [T2Space G] in
private theorem rectangleIntegrableLocalObservable
    (mu : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) :
    Integrable F (mu : Measure (Configuration d G)) := by
  apply Integrable.of_bound
    F.toContinuousMap.continuous.measurable.aestronglyMeasurable
    ‖F.toBoundedContinuousMap‖
  exact ae_of_all _ F.norm_apply_le

/-- Site reflection makes a self-closed Wilson cap literally real and
nonnegative in any neutral reflection-positive state. -/
theorem ReflectionPositiveState.siteCapsPositive
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (hp : ∀ e ∈ p.edgeSupport, k ≤ e.source τ) :
    Complex.im (∫ A, rho.wilsonLoop
      ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
        ∂(mu : Measure (Configuration d G))) = 0 ∧
    0 ≤ Complex.re (∫ A, rho.wilsonLoop
      ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
        ∂(mu : Measure (Configuration d G))) := by
  let F : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho p a
  have hfamily := hstate.siteFamilyPositive τ k F fun a =>
    holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k p hp a
  have hpair : measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) τ k F F =
      (n : ℂ) * (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
          ∂(mu : Measure (Configuration d G))) := by
    unfold F measureSiteReflectionFamilyPairing measureSiteReflectionPairing
    rw [← integral_finsetSum]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        holonomyMatrix_siteReflectionFamilyProduct_apply
          rho τ k p p hx hy A
    · intro a _ha
      exact rectangleIntegrableLocalObservable mu
        ((holonomyMatrixFlattenedComponent rho p a).siteReflectionProduct
          τ k (holonomyMatrixFlattenedComponent rho p a))
  rw [hpair] at hfamily
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  constructor
  · have him := hfamily.1
    simp only [Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero] at him
    exact (mul_eq_zero.mp him).resolve_left (by positivity)
  · have hre := hfamily.2
    simp only [Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at hre
    exact (mul_nonneg_iff_of_pos_left hn).mp hre

/-- Site-reflection Cauchy--Schwarz for two open Wilson caps in an arbitrary
neutral reflection-positive state.  The representation-dimension factors
cancel, leaving normalized Wilson-loop expectations. -/
theorem ReflectionPositiveState.siteCapsCauchySchwarz
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) {x y : Site d}
    (p q : Lattice.Cubic.Path x y)
    (hx : siteReflection τ k x = x)
    (hy : siteReflection τ k y = y)
    (hp : ∀ e ∈ p.edgeSupport, k ≤ e.source τ)
    (hq : ∀ e ∈ q.edgeSupport, k ≤ e.source τ) :
    Complex.normSq (∫ A, rho.wilsonLoop
      ((siteReflectedPathFixed τ k p hx hy).reverse.comp q) A
        ∂(mu : Measure (Configuration d G))) ≤
      Complex.re (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k p hx hy).reverse.comp p) A
          ∂(mu : Measure (Configuration d G))) *
      Complex.re (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k q hx hy).reverse.comp q) A
          ∂(mu : Measure (Configuration d G))) := by
  let F : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho p a
  let H : Fin (n * n) → LocalObservable d G := fun a =>
    holonomyMatrixFlattenedComponent rho q a
  have hfamily := hstate.siteFamilyCauchySchwarz τ k F H
    (fun a => holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k p hp a)
    (fun a => holonomyMatrixFlattenedComponent_supportedInSitePositiveHalf
      rho τ k q hq a)
  have hpair (u v : Lattice.Cubic.Path x y) :
      measureSiteReflectionFamilyPairing
          (mu : Measure (Configuration d G)) τ k
          (fun a => holonomyMatrixFlattenedComponent rho u a)
          (fun a => holonomyMatrixFlattenedComponent rho v a) =
        (n : ℂ) * (∫ A, rho.wilsonLoop
          ((siteReflectedPathFixed τ k u hx hy).reverse.comp v) A
            ∂(mu : Measure (Configuration d G))) := by
    unfold measureSiteReflectionFamilyPairing measureSiteReflectionPairing
    rw [← integral_finsetSum]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun A =>
        holonomyMatrix_siteReflectionFamilyProduct_apply
          rho τ k u v hx hy A
    · intro a _ha
      exact rectangleIntegrableLocalObservable mu
        ((holonomyMatrixFlattenedComponent rho u a).siteReflectionProduct
          τ k (holonomyMatrixFlattenedComponent rho v a))
  rw [hpair p q] at hfamily
  have hdiag (u : Lattice.Cubic.Path x y) :
      (∑ a : Fin (n * n), Complex.re (measureSiteReflectionPairing
        (mu : Measure (Configuration d G)) τ k
        (holonomyMatrixFlattenedComponent rho u a)
        (holonomyMatrixFlattenedComponent rho u a))) =
      (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
        ((siteReflectedPathFixed τ k u hx hy).reverse.comp u) A
          ∂(mu : Measure (Configuration d G))) := by
    have h := congrArg Complex.re (hpair u u)
    simp only [Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at h
    simpa [measureSiteReflectionFamilyPairing] using h
  dsimp [F, H] at hfamily
  rw [hdiag p, hdiag q] at hfamily
  have hn : (0 : ℝ) < n := by exact_mod_cast rho.dimension_pos
  simp only [Complex.normSq_mul, Complex.normSq_natCast,
    Complex.natCast_re] at hfamily
  nlinarith [sq_pos_of_pos hn]

/-! ## Half-integer planes: pointwise closed-cap geometry -/

/-- Close a mixed reflected path by the second crossing edge.  The two
crossing edges are the only data lost by the link-plane gauge fixing. -/
def linkClosedCapsPath
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ)) :
    Lattice.Cubic.Path w w :=
  let core := reflectedMixedFullPath τ k z hz p q
  let core' : Lattice.Cubic.Path w (step w (.forward τ)) :=
    YangMills.Basic.OrientedPath.castTarget
      (YangMills.Basic.OrientedPath.castSource core (by
        rw [hy]
        exact linkReflection_step_forward_eq_of_coord τ k w hw)) hu
  core'.comp (Quiver.Hom.toPath (Quiver.reverse (edgeFrom w (.forward τ))))

/-- The positive stored edge underlying the top crossing link. -/
def topCrossingPositiveEdge (w : Site d) (τ : Fin d) : PositiveEdge d :=
  ⟨w, τ⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- On the identity-crossing slice, the closed-cap holonomy drops both
crossing links. -/
theorem holonomy_linkClosedCapsPath_of_crossings_one
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ))
    (A : Configuration d G)
    (hbottom : A (crossingPositiveEdge z τ) = 1)
    (htop : A (topCrossingPositiveEdge w τ) = 1) :
    holonomy A (linkClosedCapsPath τ k z w hz hw p q hy hu) =
      holonomy A (reflectedIncomingPath τ k z hz p) * holonomy A q := by
  unfold linkClosedCapsPath reflectedMixedFullPath crossingThenPath
  rw [holonomy_comp, holonomy_castTarget, holonomy_castSource,
    holonomy_comp, holonomy_toPath, holonomy_comp, holonomy_toPath]
  have hb : signedEdgeValue A (edgeFrom z (.forward τ)).1 = 1 := by
    simpa [edgeFrom, crossingPositiveEdge] using hbottom
  have htForward : signedEdgeValue A (edgeFrom w (.forward τ)).1 = 1 := by
    simpa [edgeFrom, topCrossingPositiveEdge] using htop
  have htBase : signedEdgeValue A
      (SignedEdge.mk w (.forward τ)) = 1 := by
    simpa [edgeFrom] using htForward
  have ht : signedEdgeValue A
      (Quiver.reverse (edgeFrom w (.forward τ))).1 = 1 := by
    change signedEdgeValue A (SignedEdge.mk w (.forward τ)).reverse = 1
    rw [signedEdgeValue_reverse, htBase, inv_one]
  rw [hb, ht]
  group

/-- The unnormalized Wilson loop around two link-reflected caps. -/
def linkClosedCapsObservable
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ)) : LocalObservable d G :=
  LocalObservable.smul (n : ℂ)
    (rho.wilsonLoop (linkClosedCapsPath τ k z w hz hw p q hy hu))

@[simp]
theorem linkClosedCapsObservable_apply
    (rho : ContinuousUnitaryRepData G n)
    (τ : Fin d) (k : ℤ) (z w : Site d)
    (hz : z τ = k) (hw : w τ = k)
    {y u : Site d}
    (p : Lattice.Cubic.Path (step z (.forward τ)) y)
    (q : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hy : y = step w (.forward τ))
    (hu : u = step w (.forward τ))
    (A : Configuration d G) :
    linkClosedCapsObservable rho τ k z w hz hw p q hy hu A =
      (n : ℂ) * rho.wilsonLoop
        (linkClosedCapsPath τ k z w hz hw p q hy hu) A :=
  rfl

end

end YangMills.Gluelump.Propagation
