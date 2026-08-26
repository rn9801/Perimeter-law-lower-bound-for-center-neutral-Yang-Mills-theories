/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ConjugationSpanScreenedWilsonLine
import GluelumpPerimeterLaw.OneLink.ConjugationSpanOneLinkObservableCore
import GluelumpPerimeterLaw.Propagation.ReflectedLineMixedCore
import GluelumpPerimeterLaw.Propagation.SiteReflectedLine
import GluelumpPerimeterLaw.Propagation.StraightGeometryCore
import GluelumpPerimeterLaw.Propagation.StraightLine
import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState

/-!
# Direct conjugation-span straight lines indexed by physical length

The old straight-line propagation sequence is indexed by a half-arm length,
so its `l`th member has physical length `2*l+1`.  This file instead defines
one observable for every physical length.  Odd lengths are norm squares for
the link reflection through `x_a = 1/2`; even lengths are norm squares for
the site reflection through `x_a = 0`.

All endpoint copies are translations of one normalized direct
conjugation-span endpoint at the first positive arm site.  In particular no
length-dependent normalization is introduced, and the physical one-link
member is exactly the one-link observable used by the strict-positivity
argument.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## One normalized endpoint and all of its axial translates -/

/-- The direct endpoint at the first site on the positive arm. -/
def conjSpanStraightBaseEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) : LocalField d G (Fin r → ℂ) :=
  conjSpanPhi hd sigma rho T
    (step z (.forward (Geometry.armAxis hd)))

/-- Translate the single normalized base endpoint `l` steps farther into the
positive arm half-space.  Its base site is at arm distance `l+1` from `z`. -/
def conjSpanLinkStraightEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanStraightBaseEndpoint hd sigma rho T z).translatePullback
    (l • unitVector (Geometry.armAxis hd))

/-- Translate the same endpoint to arm distance `l` from `z`.  The integer
shift `l-1` also covers `l=0`, where the endpoint is centered in the site
reflection plane. -/
def conjSpanSiteStraightEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanStraightBaseEndpoint hd sigma rho T z).translatePullback
    (((l : ℤ) - 1) • unitVector (Geometry.armAxis hd))

theorem conjSpanLinkStraightEndpoint_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) :
    GaugeCovariantAt rho
      (Path.advance (step z (.forward (Geometry.armAxis hd)))
        (.forward (Geometry.armAxis hd)) l)
      (conjSpanLinkStraightEndpoint hd sigma rho T z l) := by
  have htarget :
      Lattice.Cubic.translate (l • unitVector (Geometry.armAxis hd))
          (step z (.forward (Geometry.armAxis hd))) =
        Path.advance (step z (.forward (Geometry.armAxis hd)))
          (.forward (Geometry.armAxis hd)) l := by
    rw [Path.advance_eq]
    simp [Lattice.Cubic.translate, SignedDirection.delta_forward]
  rw [← htarget]
  exact (conjSpanPhi_gauge_covariant hd sigma rho T
    (step z (.forward (Geometry.armAxis hd)))).translatePullback
      rho _ _ (l • unitVector (Geometry.armAxis hd))

theorem conjSpanLinkStraightEndpoint_supportedInLinkPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    (conjSpanLinkStraightEndpoint hd sigma rho T z l).SupportedInLinkPositiveHalf
      (Geometry.armAxis hd) 0 := by
  intro e he
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T z).support.image
    (PositiveEdge.translate
      (l • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step z (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have hp := basedLoopSupport_combLoops_armPlane hd
    (step z (.forward (Geometry.armAxis hd))) e₀ he₀
  rw [PositiveEdge.target_translate]
  simp [Lattice.Cubic.translate, unitVector, step,
    SignedDirection.forward, SignedDirection.delta, hz, hp.2]
  omega

/-! ## Link-centered odd lines -/

/-- The link-reflection norm square of physical length `2*l+1`. -/
def conjSpanLinkStraightObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    LocalObservable d G :=
  let a := Geometry.armAxis hd
  let Phi := conjSpanLinkStraightEndpoint hd sigma rho T z l
  screenedObservable rho (Phi.linkPullback a 0) Phi
    (reflectedFullPath a 0 z hz (straightPositiveHalfPath a z l))

/-- The mixed link-reflection contraction of positive half-arms of lengths
`l` and `s`; its transport path has physical length `l+s+1`. -/
def conjSpanLinkStraightMixedObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l s : ℕ) :
    LocalObservable d G :=
  let a := Geometry.armAxis hd
  reflectedMixedObservable rho
    (conjSpanLinkStraightEndpoint hd sigma rho T z l)
    (conjSpanLinkStraightEndpoint hd sigma rho T z s)
    a 0 z hz (straightPositiveHalfPath a z l)
      (straightPositiveHalfPath a z s)

/-- The physical one-link member is pointwise the direct reflected one-link
seed used by the strict-positivity theorem. -/
theorem conjSpanLinkStraightObservable_zero_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (A : Configuration d G) :
    conjSpanLinkStraightObservable hd sigma rho T z hz 0 A =
      conjSpanReflectedOneLinkObservable hd sigma rho T z hz A := by
  simp only [conjSpanLinkStraightObservable,
    conjSpanLinkStraightEndpoint, conjSpanStraightBaseEndpoint,
    conjSpanReflectedOneLinkObservable,
    screenedObservable_apply, screenedValue, zero_smul,
    LocalField.linkPullback_apply, LocalField.translatePullback_apply,
    LocalObservable.translateConfiguration_zero,
    reflectedEndpointOneLinkObservable]

theorem norm_conjSpanLinkStraightObservable_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    ‖conjSpanLinkStraightObservable hd sigma rho T z hz l A‖ ≤ 1 := by
  apply norm_screenedValue_le_one
  · rw [LocalField.linkPullback_apply]
    change endpointL2Norm (conjSpanPhi hd sigma rho T _ _) ≤ 1
    exact conjSpanPhi_l2Norm_le_one hd sigma rho T _ _
  · change endpointL2Norm (conjSpanPhi hd sigma rho T _ _) ≤ 1
    exact conjSpanPhi_l2Norm_le_one hd sigma rho T _ _

/-! ## Site-centered even lines -/

/-- The positive half of an even line, running from the site-reflection
plane to the endpoint at arm distance `l`. -/
def conjSpanSiteStraightHalfPath
    (hd : 3 ≤ d) (z : Site d) (l : ℕ) :
    Lattice.Cubic.Path z
      (Path.advance z (.forward (Geometry.armAxis hd)) l) :=
  Path.straight z (.forward (Geometry.armAxis hd)) l

theorem conjSpanSiteStraightHalfPath_supportedInSitePositiveHalf
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    Endpoint.Path.SupportedInSitePositiveHalf (Geometry.armAxis hd) 0
      (conjSpanSiteStraightHalfPath hd z l) := by
  intro e he
  have hbounds := straight_forward_edgeSupport_coordinate_bounds
    z (Geometry.armAxis hd) l e he
  omega

theorem conjSpanSiteStraightEndpoint_target
    (hd : 3 ≤ d) (z : Site d) (l : ℕ) :
    Lattice.Cubic.translate
        (((l : ℤ) - 1) • unitVector (Geometry.armAxis hd))
        (step z (.forward (Geometry.armAxis hd))) =
      Path.advance z (.forward (Geometry.armAxis hd)) l := by
  rw [Path.advance_eq]
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector]
  · simp [Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hi]

theorem conjSpanSiteStraightEndpoint_covariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) :
    GaugeCovariantAt rho
      (Path.advance z (.forward (Geometry.armAxis hd)) l)
      (conjSpanSiteStraightEndpoint hd sigma rho T z l) := by
  rw [← conjSpanSiteStraightEndpoint_target hd z l]
  exact (conjSpanPhi_gauge_covariant hd sigma rho T
    (step z (.forward (Geometry.armAxis hd)))).translatePullback
      rho _ _ (((l : ℤ) - 1) • unitVector (Geometry.armAxis hd))

theorem conjSpanSiteStraightEndpoint_supportedInSitePositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    (conjSpanSiteStraightEndpoint hd sigma rho T z l).SupportedInSitePositiveHalf
      (Geometry.armAxis hd) 0 := by
  intro e he
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T z).support.image
    (PositiveEdge.translate
      (((l : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step z (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have hp := basedLoopSupport_combLoops_armPlane hd
    (step z (.forward (Geometry.armAxis hd))) e₀ he₀
  rw [PositiveEdge.source_translate]
  simp [Lattice.Cubic.translate, unitVector, step,
    SignedDirection.forward, SignedDirection.delta, hz, hp.1]

/-- Translating an integer-reflected configuration by `l-1` arm units is
the same as translating the adjacent link-reflected configuration by `l`
arm units.  This is the endpoint identity behind the site/link parity
transition. -/
theorem translate_pred_siteReflectConfiguration_eq_translate_linkReflectConfiguration
    (tau : Fin d) (l : ℕ) (A : Configuration d G) :
    LocalObservable.translateConfiguration
        (((l : ℤ) - 1) • unitVector tau)
        (siteReflectConfiguration tau 0 A) =
      LocalObservable.translateConfiguration (l • unitVector tau)
        (linkReflectConfiguration tau 0 A) := by
  funext e
  have hedge :
      (e.translate (((l : ℤ) - 1) • unitVector tau)).siteReflect tau 0 =
        (e.translate (l • unitVector tau)).linkReflect tau 0 := by
    rcases e with ⟨x, i⟩
    by_cases hi : i = tau
    · subst i
      simp only [PositiveEdge.translate, PositiveEdge.siteReflect,
        PositiveEdge.linkReflect, if_pos]
      congr 1
      ext j
      by_cases hj : j = tau
      · subst j
        simp [Lattice.Cubic.translate, PositiveEdge.target, siteReflection,
          linkReflection, step, SignedDirection.forward,
          SignedDirection.delta, unitVector]
        ring
      · simp [Lattice.Cubic.translate, PositiveEdge.target, siteReflection,
          linkReflection, step, SignedDirection.forward,
          SignedDirection.delta, unitVector, hj]
    · simp only [PositiveEdge.translate, PositiveEdge.siteReflect,
        PositiveEdge.linkReflect, hi, if_false]
      congr 1
      ext j
      by_cases hj : j = tau
      · subst j
        simp [Lattice.Cubic.translate, siteReflection, linkReflection,
          unitVector]
        ring
      · simp [Lattice.Cubic.translate, siteReflection, linkReflection,
          unitVector, hj]
  change (if (e.translate (((l : ℤ) - 1) • unitVector tau)).direction = tau
      then (A ((e.translate (((l : ℤ) - 1) • unitVector tau)).siteReflect
        tau 0))⁻¹
      else A ((e.translate (((l : ℤ) - 1) • unitVector tau)).siteReflect
        tau 0)) =
    (if (e.translate (l • unitVector tau)).direction = tau
      then (A ((e.translate (l • unitVector tau)).linkReflect tau 0))⁻¹
      else A ((e.translate (l • unitVector tau)).linkReflect tau 0))
  rw [hedge]
  rfl

theorem conjSpanSiteStraightEndpoint_sitePullback_apply_eq_linkPullback
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) (A : Configuration d G) :
    (conjSpanSiteStraightEndpoint hd sigma rho T z l).sitePullback
        (Geometry.armAxis hd) 0 A =
      (conjSpanLinkStraightEndpoint hd sigma rho T z l).linkPullback
        (Geometry.armAxis hd) 0 A := by
  simp only [conjSpanSiteStraightEndpoint, conjSpanLinkStraightEndpoint,
    LocalField.sitePullback_apply, LocalField.linkPullback_apply,
    LocalField.translatePullback_apply]
  rw [translate_pred_siteReflectConfiguration_eq_translate_linkReflectConfiguration]

theorem conjSpanSiteStraightEndpoint_succ_apply_eq_linkEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) (A : Configuration d G) :
    conjSpanSiteStraightEndpoint hd sigma rho T z (l + 1) A =
      conjSpanLinkStraightEndpoint hd sigma rho T z l A := by
  simp only [conjSpanSiteStraightEndpoint, conjSpanLinkStraightEndpoint,
    LocalField.translatePullback_apply]
  congr 2
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [unitVector]
  · simp [unitVector, hi]

/-- The site-reflection norm square of physical length `2*l`. -/
def conjSpanSiteStraightObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    LocalObservable d G :=
  siteReflectedObservable rho
    (conjSpanSiteStraightEndpoint hd sigma rho T z l)
    (Geometry.armAxis hd) 0 z hz (conjSpanSiteStraightHalfPath hd z l)

/-- The mixed site-reflection contraction of positive halves of radii `l`
and `s`; its transport path has physical length `l+s`. -/
def conjSpanSiteStraightMixedObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l s : ℕ) :
    LocalObservable d G :=
  siteReflectedMixedObservable rho
    (conjSpanSiteStraightEndpoint hd sigma rho T z l)
    (conjSpanSiteStraightEndpoint hd sigma rho T z s)
    (Geometry.armAxis hd) 0 z hz
    (conjSpanSiteStraightHalfPath hd z l)
    (conjSpanSiteStraightHalfPath hd z s)

theorem siteReflection_advance_eq_linkReflection_advance_step
    (tau : Fin d) (z : Site d) (hz : z tau = 0) (l : ℕ) :
    siteReflection tau 0 (Path.advance z (.forward tau) l) =
      linkReflection tau 0
        (Path.advance (step z (.forward tau)) (.forward tau) l) := by
  ext i
  by_cases hi : i = tau
  · subst i
    simp [Path.advance_eq, siteReflection, linkReflection,
      Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hz]
  · simp [Path.advance_eq, siteReflection, linkReflection,
      Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hi]

theorem advance_succ_eq_advance_step
    (tau : Fin d) (z : Site d) (l : ℕ) :
    Path.advance z (.forward tau) (l + 1) =
      Path.advance (step z (.forward tau)) (.forward tau) l := by
  rw [Path.advance_eq, Path.advance_eq]
  ext i
  by_cases hi : i = tau <;>
    simp [step, SignedDirection.forward, SignedDirection.delta,
      unitVector, hi] <;> omega

/-- Recast the site-mixed path of radii `l,l+1` to the endpoint types of the
link-reflected self-line of half-length `l`. -/
def siteMixedAdjacentPathAsLink
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    Lattice.Cubic.Path
      (linkReflection (Geometry.armAxis hd) 0
        (Path.advance (step z (.forward (Geometry.armAxis hd)))
          (.forward (Geometry.armAxis hd)) l))
      (Path.advance (step z (.forward (Geometry.armAxis hd)))
        (.forward (Geometry.armAxis hd)) l) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (siteReflectedMixedFullPath (Geometry.armAxis hd) 0 z hz
        (conjSpanSiteStraightHalfPath hd z l)
        (conjSpanSiteStraightHalfPath hd z (l + 1)))
      (siteReflection_advance_eq_linkReflection_advance_step
        (Geometry.armAxis hd) z hz l))
    (advance_succ_eq_advance_step (Geometry.armAxis hd) z l)

@[simp]
theorem directions_siteReflect_physicalStraight
    {x y : Site d} (tau : Fin d) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.siteReflect tau k).directions =
      p.directions.map (SignedDirection.siteReflect tau) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Path.directions ((siteReflectionPrefunctor tau k).mapPath p) = _ at ih
      change Path.directions (((siteReflectionPrefunctor tau k).mapPath p).cons
        ((siteReflectionPrefunctor tau k).map e)) = _
      rw [Path.directions_cons, ih, Path.directions_cons,
        List.map_append, List.map_singleton]
      rfl

@[simp]
theorem directions_linkReflect_eq_siteReflect_physicalStraight
    {x y : Site d} (tau : Fin d) (k : ℤ)
    (p : Lattice.Cubic.Path x y) :
    (p.linkReflect tau k).directions = (p.siteReflect tau k).directions := by
  unfold Path.linkReflect
  exact Path.directions_translate (unitVector tau) (p.siteReflect tau k)

theorem siteMixedAdjacentPathAsLink_eq_reflectedFullPath
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    siteMixedAdjacentPathAsLink hd z hz l =
      reflectedFullPath (Geometry.armAxis hd) 0 z hz
        (straightPositiveHalfPath (Geometry.armAxis hd) z l) := by
  apply Path.ext_directions
  simp [siteMixedAdjacentPathAsLink, siteReflectedMixedFullPath,
    siteReflectedIncomingPath, reflectedFullPath, reflectedIncomingPath,
    crossingThenPath, conjSpanSiteStraightHalfPath,
    straightPositiveHalfPath, SignedDirection.siteReflect,
    SignedDirection.forward, SignedDirection.backward,
    directions_siteReflect_physicalStraight,
    directions_linkReflect_eq_siteReflect_physicalStraight,
    List.reverse_replicate, List.replicate_succ, List.append_assoc]

theorem holonomy_siteMixedAdjacent_eq_linkFull
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    holonomy A
        (siteReflectedMixedFullPath (Geometry.armAxis hd) 0 z hz
          (conjSpanSiteStraightHalfPath hd z l)
          (conjSpanSiteStraightHalfPath hd z (l + 1))) =
      holonomy A
        (reflectedFullPath (Geometry.armAxis hd) 0 z hz
          (straightPositiveHalfPath (Geometry.armAxis hd) z l)) := by
  rw [← siteMixedAdjacentPathAsLink_eq_reflectedFullPath hd z hz l]
  simp [siteMixedAdjacentPathAsLink]

/-- The site mixed pairing between radii `l` and `l+1` is exactly the odd
physical line between the neighboring even self-lines. -/
theorem conjSpanSiteStraightMixed_succ_apply_eq_linkStraight
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    conjSpanSiteStraightMixedObservable hd sigma rho T z hz l (l + 1) A =
      conjSpanLinkStraightObservable hd sigma rho T z hz l A := by
  rw [conjSpanSiteStraightMixedObservable,
    siteReflectedMixedObservable, conjSpanLinkStraightObservable,
    screenedObservable_apply, screenedObservable_apply]
  unfold screenedValue
  rw [conjSpanSiteStraightEndpoint_sitePullback_apply_eq_linkPullback,
    conjSpanSiteStraightEndpoint_succ_apply_eq_linkEndpoint,
    holonomy_siteMixedAdjacent_eq_linkFull]

theorem conjSpanSiteStraightEndpoint_succ_apply_translate_eq_linkEndpoint_succ
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) (A : Configuration d G) :
    conjSpanSiteStraightEndpoint hd sigma rho T z (l + 1)
        (LocalObservable.translateConfiguration
          (unitVector (Geometry.armAxis hd)) A) =
      conjSpanLinkStraightEndpoint hd sigma rho T z (l + 1) A := by
  simp only [conjSpanSiteStraightEndpoint, conjSpanLinkStraightEndpoint,
    LocalField.translatePullback_apply,
    LocalObservable.translateConfiguration_translateConfiguration]
  congr 2
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [unitVector]
  · simp [unitVector, hi]

theorem conjSpanSiteStraightEndpoint_succ_sitePullback_apply_translate_eq_linkPullback
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (l : ℕ) (A : Configuration d G) :
    (conjSpanSiteStraightEndpoint hd sigma rho T z (l + 1)).sitePullback
        (Geometry.armAxis hd) 0
        (LocalObservable.translateConfiguration
          (unitVector (Geometry.armAxis hd)) A) =
      (conjSpanLinkStraightEndpoint hd sigma rho T z l).linkPullback
        (Geometry.armAxis hd) 0 A := by
  simp only [conjSpanSiteStraightEndpoint, conjSpanLinkStraightEndpoint,
    LocalField.sitePullback_apply, LocalField.linkPullback_apply,
    LocalField.translatePullback_apply]
  rw [linkReflectConfiguration_eq_siteReflect_translate]
  congr 2
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [unitVector]
  · simp [unitVector, hi]

theorem translated_siteReflection_advance_succ_eq_linkReflection_advance_step
    (tau : Fin d) (z : Site d) (hz : z tau = 0) (l : ℕ) :
    Lattice.Cubic.translate (unitVector tau)
        (siteReflection tau 0 (Path.advance z (.forward tau) (l + 1))) =
      linkReflection tau 0
        (Path.advance (step z (.forward tau)) (.forward tau) l) := by
  ext i
  by_cases hi : i = tau
  · subst i
    simp [Path.advance_eq, siteReflection, linkReflection,
      Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hz]
  · simp [Path.advance_eq, siteReflection, linkReflection,
      Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hi]

theorem translated_advance_succ_eq_advance_step_succ
    (tau : Fin d) (z : Site d) (l : ℕ) :
    Lattice.Cubic.translate (unitVector tau)
        (Path.advance z (.forward tau) (l + 1)) =
      Path.advance (step z (.forward tau)) (.forward tau) (l + 1) := by
  rw [Path.advance_eq, Path.advance_eq]
  ext i
  by_cases hi : i = tau <;>
    simp [Lattice.Cubic.translate, step, SignedDirection.forward,
      SignedDirection.delta, unitVector, hi] <;> omega

/-- The site-reflected even self-line of radius `l+1`, translated one arm
unit, recast to the endpoint types of the link-mixed pair `(l,l+1)`. -/
def translatedSiteFullPathAsLinkMixed
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    Lattice.Cubic.Path
      (linkReflection (Geometry.armAxis hd) 0
        (Path.advance (step z (.forward (Geometry.armAxis hd)))
          (.forward (Geometry.armAxis hd)) l))
      (Path.advance (step z (.forward (Geometry.armAxis hd)))
        (.forward (Geometry.armAxis hd)) (l + 1)) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      ((siteReflectedFullPath (Geometry.armAxis hd) 0 z hz
        (conjSpanSiteStraightHalfPath hd z (l + 1))).translate
          (unitVector (Geometry.armAxis hd)))
      (translated_siteReflection_advance_succ_eq_linkReflection_advance_step
        (Geometry.armAxis hd) z hz l))
    (translated_advance_succ_eq_advance_step_succ
      (Geometry.armAxis hd) z l)

theorem translatedSiteFullPathAsLinkMixed_eq_reflectedMixedFullPath
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    translatedSiteFullPathAsLinkMixed hd z hz l =
      reflectedMixedFullPath (Geometry.armAxis hd) 0 z hz
        (straightPositiveHalfPath (Geometry.armAxis hd) z l)
        (straightPositiveHalfPath (Geometry.armAxis hd) z (l + 1)) := by
  apply Path.ext_directions
  simp [translatedSiteFullPathAsLinkMixed, siteReflectedFullPath,
    siteReflectedMixedFullPath, siteReflectedIncomingPath,
    reflectedMixedFullPath, reflectedIncomingPath, crossingThenPath,
    conjSpanSiteStraightHalfPath, straightPositiveHalfPath,
    directions_siteReflect_physicalStraight,
    directions_linkReflect_eq_siteReflect_physicalStraight,
    SignedDirection.siteReflect, SignedDirection.forward,
    SignedDirection.backward, List.reverse_replicate,
    List.replicate_succ, List.append_assoc]

theorem holonomy_translatedSiteFull_eq_linkMixed
    (hd : 3 ≤ d) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    holonomy
        (LocalObservable.translateConfiguration
          (unitVector (Geometry.armAxis hd)) A)
        (siteReflectedFullPath (Geometry.armAxis hd) 0 z hz
          (conjSpanSiteStraightHalfPath hd z (l + 1))) =
      holonomy A
        (reflectedMixedFullPath (Geometry.armAxis hd) 0 z hz
          (straightPositiveHalfPath (Geometry.armAxis hd) z l)
          (straightPositiveHalfPath (Geometry.armAxis hd) z (l + 1))) := by
  change holonomy (fun e => A (e.translate (unitVector (Geometry.armAxis hd))))
      (siteReflectedFullPath (Geometry.armAxis hd) 0 z hz
        (conjSpanSiteStraightHalfPath hd z (l + 1))) = _
  rw [holonomy_translateConfiguration]
  have hcast :
      holonomy A
          ((siteReflectedFullPath (Geometry.armAxis hd) 0 z hz
            (conjSpanSiteStraightHalfPath hd z (l + 1))).translate
              (unitVector (Geometry.armAxis hd))) =
        holonomy A (translatedSiteFullPathAsLinkMixed hd z hz l) := by
    simp [translatedSiteFullPathAsLinkMixed]
  rw [hcast]
  rw [translatedSiteFullPathAsLinkMixed_eq_reflectedMixedFullPath]

/-- The link mixed pairing between half-lengths `l,l+1` is the translated
even physical line between the neighboring odd self-lines. -/
theorem conjSpanSiteStraight_succ_translate_apply_eq_linkMixed
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    conjSpanSiteStraightObservable hd sigma rho T z hz (l + 1)
        (LocalObservable.translateConfiguration
          (unitVector (Geometry.armAxis hd)) A) =
      conjSpanLinkStraightMixedObservable hd sigma rho T z hz l (l + 1) A := by
  rw [conjSpanSiteStraightObservable, siteReflectedObservable,
    siteReflectedMixedObservable, conjSpanLinkStraightMixedObservable,
    reflectedMixedObservable, screenedObservable_apply,
    screenedObservable_apply]
  unfold screenedValue
  rw [conjSpanSiteStraightEndpoint_succ_sitePullback_apply_translate_eq_linkPullback,
    conjSpanSiteStraightEndpoint_succ_apply_translate_eq_linkEndpoint_succ]
  have hhol := holonomy_translatedSiteFull_eq_linkMixed hd z hz l A
  unfold siteReflectedFullPath at hhol
  rw [hhol]

theorem norm_conjSpanSiteStraightObservable_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ)
    (A : Configuration d G) :
    ‖conjSpanSiteStraightObservable hd sigma rho T z hz l A‖ ≤ 1 := by
  apply norm_screenedValue_le_one
  · rw [LocalField.sitePullback_apply]
    change endpointL2Norm (conjSpanPhi hd sigma rho T _ _) ≤ 1
    exact conjSpanPhi_l2Norm_le_one hd sigma rho T _ _
  · change endpointL2Norm (conjSpanPhi hd sigma rho T _ _) ≤ 1
    exact conjSpanPhi_l2Norm_le_one hd sigma rho T _ _

/-! ## One observable for every physical length -/

/-- The canonical direct screened line indexed by its actual number of arm
bonds.  Even lengths use a site cut and odd lengths use the adjacent link
cut. -/
def conjSpanPhysicalStraightObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ) :
    LocalObservable d G :=
  if Even length then
    conjSpanSiteStraightObservable hd sigma rho T z hz (length / 2)
  else
    conjSpanLinkStraightObservable hd sigma rho T z hz (length / 2)

@[simp]
theorem conjSpanPhysicalStraightObservable_even
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    conjSpanPhysicalStraightObservable hd sigma rho T z hz (2 * l) =
      conjSpanSiteStraightObservable hd sigma rho T z hz l := by
  simp [conjSpanPhysicalStraightObservable]

@[simp]
theorem conjSpanPhysicalStraightObservable_odd
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (l : ℕ) :
    conjSpanPhysicalStraightObservable hd sigma rho T z hz (2 * l + 1) =
      conjSpanLinkStraightObservable hd sigma rho T z hz l := by
  unfold conjSpanPhysicalStraightObservable
  rw [if_neg (Nat.not_even_two_mul_add_one l)]
  congr
  omega

/-- The member at physical length one is literally the strict-positive
direct one-link seed, pointwise. -/
theorem conjSpanPhysicalStraightObservable_one_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (A : Configuration d G) :
    conjSpanPhysicalStraightObservable hd sigma rho T z hz 1 A =
      conjSpanReflectedOneLinkObservable hd sigma rho T z hz A := by
  simpa using
    conjSpanLinkStraightObservable_zero_apply hd sigma rho T z hz A

theorem norm_conjSpanPhysicalStraightObservable_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) (length : ℕ)
    (A : Configuration d G) :
    ‖conjSpanPhysicalStraightObservable hd sigma rho T z hz length A‖ ≤ 1 := by
  rcases Nat.even_or_odd' length with ⟨l, rfl | rfl⟩
  · simpa using norm_conjSpanSiteStraightObservable_le_one
      hd sigma rho T z hz l A
  · simpa using norm_conjSpanLinkStraightObservable_le_one
      hd sigma rho T z hz l A

end

end YangMills.Gluelump.Propagation
