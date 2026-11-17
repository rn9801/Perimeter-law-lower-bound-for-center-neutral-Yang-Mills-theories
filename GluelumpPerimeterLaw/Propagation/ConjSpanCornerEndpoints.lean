/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ConjSpanCornerGeometry
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraight

/-!
# Direct endpoint copies for the affine corner geometry

This module places the one normalized conjugation-span endpoint at the far
vertex of the affine square.  Site reflection gives the left endpoint of an
even physical line and link reflection gives the left endpoint of an odd
physical line.  The pointwise identities below connect these copies directly
to the physical-length family.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The proof that the zero site lies on the physical family's central arm
plane. -/
def conjSpanCornerZeroArm (hd : 3 ≤ d) :
    (0 : Site d) (Geometry.armAxis hd) = 0 := rfl

/-- The single normalized base endpoint, translated so that its base site is
`t e_a`. -/
def conjSpanCornerFarEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (t : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).translatePullback
    (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))

/-- The left endpoint of the even physical line of length `2*l`. -/
def conjSpanEvenCornerOriginEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanCornerFarEndpoint hd sigma rho T l).sitePullback
    (Geometry.armAxis hd) 0

/-- The left endpoint of the odd physical line of length `2*l+1`. -/
def conjSpanOddCornerOriginEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanCornerFarEndpoint hd sigma rho T (l + 1)).linkPullback
    (Geometry.armAxis hd) 0

/-- The comparison collar used to bend an even physical line. -/
def conjSpanEvenCornerComparisonEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanEvenCornerOriginEndpoint hd sigma rho T l).diagonalPullback
    (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) (-(l : ℤ))

/-- The comparison collar used to bend an odd physical line. -/
def conjSpanOddCornerComparisonEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanOddCornerOriginEndpoint hd sigma rho T l).diagonalPullback
    (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) (-(l : ℤ))

/-! ## Collar support at the affine corner -/

/-- Every edge of the translated direct collar has arm coordinate `t` and
first transverse coordinate in `[0,m]`. -/
theorem conjSpanCornerFarEndpoint_support_coordinates
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (t : ℕ) {e : PositiveEdge d}
    (he : e ∈ (conjSpanCornerFarEndpoint hd sigma rho T t).support) :
    e.source (Geometry.armAxis hd) = t ∧
      e.target (Geometry.armAxis hd) = t ∧
      0 ≤ e.source (Geometry.transverseAxis₁ hd) ∧
      e.source (Geometry.transverseAxis₁ hd) ≤ m ∧
      0 ≤ e.target (Geometry.transverseAxis₁ hd) ∧
      e.target (Geometry.transverseAxis₁ hd) ≤ m := by
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).support.image
    (PositiveEdge.translate
      (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step (0 : Site d) (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have harm := basedLoopSupport_combLoops_armPlane hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  have htrans := basedLoopSupport_combLoops_transverseAxis₁_bounds hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  simp [PositiveEdge.source_translate, PositiveEdge.target_translate,
    Lattice.Cubic.translate, step, SignedDirection.forward,
    SignedDirection.delta, unitVector,
    Geometry.armAxis_ne_transverseAxis₁ hd,
    (Geometry.armAxis_ne_transverseAxis₁ hd).symm] at harm htrans ⊢
  omega

/-- Once the physical arm length `s+t` dominates the collar width, the far
endpoint lies on the positive side of the bending diagonal. -/
theorem conjSpanCornerFarEndpoint_supportedInDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (s t : ℕ) (hm : m ≤ s + t) :
    (conjSpanCornerFarEndpoint hd sigma rho T t).SupportedInDiagonalPositiveHalf
        (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) (-(s : ℤ)) := by
  intro e he
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).support.image
    (PositiveEdge.translate
      (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step (0 : Site d) (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have harm := basedLoopSupport_combLoops_armPlane hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  have htrans := basedLoopSupport_combLoops_transverseAxis₁_bounds hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  simp only [Pi.zero_apply, zero_add] at harm htrans
  simp [PositiveEdge.source_translate, PositiveEdge.target_translate,
    Lattice.Cubic.translate, step, SignedDirection.forward,
    SignedDirection.delta, unitVector,
    Geometry.armAxis_ne_transverseAxis₁ hd,
    (Geometry.armAxis_ne_transverseAxis₁ hd).symm] at harm htrans ⊢
  omega

/-- The far endpoint is automatically on the positive side of the closing
anti-diagonal through its base point. -/
theorem conjSpanCornerFarEndpoint_supportedInAntiDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (t : ℕ) :
    (conjSpanCornerFarEndpoint hd sigma rho T t).SupportedInAntiDiagonalPositiveHalf
        (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) t := by
  intro e he
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).support.image
    (PositiveEdge.translate
      (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step (0 : Site d) (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have harm := basedLoopSupport_combLoops_armPlane hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  have htrans := basedLoopSupport_combLoops_transverseAxis₁_bounds hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  simp only [Pi.zero_apply, zero_add] at harm htrans
  simp [PositiveEdge.source_translate, PositiveEdge.target_translate,
    Lattice.Cubic.translate, step, SignedDirection.forward,
    SignedDirection.delta, unitVector,
    Geometry.armAxis_ne_transverseAxis₁ hd,
    (Geometry.armAxis_ne_transverseAxis₁ hd).symm] at harm htrans ⊢
  omega

/-- Bending the far collar through `x_a-x_b=-s` places it on the positive
side of the closing anti-diagonal `x_a+x_b=t`. -/
theorem conjSpanCornerFarEndpoint_diagonalPullback_supportedInAntiDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (s t : ℕ) :
    Endpoint.LocalField.SupportedInAntiDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) t
      ((conjSpanCornerFarEndpoint hd sigma rho T t).diagonalPullback
        (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) (-(s : ℤ))) := by
  intro e he
  change e ∈ (conjSpanCornerFarEndpoint hd sigma rho T t).support.image
    (PositiveEdge.diagonalReflect (Geometry.armAxis hd)
      (Geometry.transverseAxis₁ hd) (-(s : ℤ))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).support.image
    (PositiveEdge.translate
      (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he₀
  rcases Finset.mem_image.mp he₀ with ⟨e₁, he₁, rfl⟩
  change e₁ ∈ (conjSpanPhi hd sigma rho T
    (step (0 : Site d) (.forward (Geometry.armAxis hd)))).support at he₁
  rw [conjSpanPhi_support] at he₁
  have harm := basedLoopSupport_combLoops_armPlane hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₁ he₁
  have htrans := basedLoopSupport_combLoops_transverseAxis₁_bounds hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₁ he₁
  simp only [Pi.zero_apply, zero_add] at harm htrans
  simp [PositiveEdge.source_diagonalReflect,
    PositiveEdge.target_diagonalReflect,
    PositiveEdge.source_translate, PositiveEdge.target_translate,
    Lattice.Cubic.translate, step, SignedDirection.forward,
    SignedDirection.delta, unitVector,
    Geometry.armAxis_ne_transverseAxis₁ hd,
    (Geometry.armAxis_ne_transverseAxis₁ hd).symm] at harm htrans ⊢
  omega

/-- The diagonal comparison copy of the link-reflected odd endpoint lies in
the bending positive algebra. -/
theorem conjSpanOddCornerComparisonEndpoint_supportedInDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) :
    (conjSpanOddCornerComparisonEndpoint hd sigma rho T l).SupportedInDiagonalPositiveHalf
        (Geometry.armAxis hd) (Geometry.transverseAxis₁ hd) (-(l : ℤ)) := by
  have hab : Geometry.armAxis hd ≠ Geometry.transverseAxis₁ hd :=
    Geometry.armAxis_ne_transverseAxis₁ hd
  intro e he
  change e ∈ (conjSpanOddCornerOriginEndpoint hd sigma rho T l).support.image
    (PositiveEdge.diagonalReflect (Geometry.armAxis hd)
      (Geometry.transverseAxis₁ hd) (-(l : ℤ))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanCornerFarEndpoint hd sigma rho T (l + 1)).support.image
    (PositiveEdge.linkReflect (Geometry.armAxis hd) 0) at he₀
  rcases Finset.mem_image.mp he₀ with ⟨e₁, he₁, rfl⟩
  have hc := conjSpanCornerFarEndpoint_support_coordinates
    hd sigma rho T (l + 1) he₁
  rcases PositiveEdge.linkReflect_endpoints
      (Geometry.armAxis hd) 0 e₁ with hend | hend
  · rw [PositiveEdge.source_diagonalReflect,
      PositiveEdge.target_diagonalReflect hab, hend.1, hend.2]
    simp [diagonalReflection, linkReflection, siteReflection,
      Lattice.Cubic.translate, unitVector, hab, hab.symm] at hc ⊢
    omega
  · rw [PositiveEdge.source_diagonalReflect,
      PositiveEdge.target_diagonalReflect hab, hend.1, hend.2]
    simp [diagonalReflection, linkReflection, siteReflection,
      Lattice.Cubic.translate, unitVector, hab, hab.symm] at hc ⊢
    omega

/-! ## The physical reflected paths are the affine straight arms -/

theorem advance_zero_forward_eq_conjSpanCornerFarSite
    (hd : 3 ≤ d) (t : ℕ) :
    Path.advance (0 : Site d) (.forward (Geometry.armAxis hd)) t =
      conjSpanCornerFarSite (Geometry.armAxis hd) t := by
  rw [Path.advance_eq]
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [conjSpanCornerFarSite, SignedDirection.delta_forward, unitVector]
  · simp [conjSpanCornerFarSite, SignedDirection.delta_forward, unitVector, hi]

theorem advance_step_zero_forward_eq_conjSpanCornerFarSite_succ
    (hd : 3 ≤ d) (l : ℕ) :
    Path.advance (step (0 : Site d) (.forward (Geometry.armAxis hd)))
        (.forward (Geometry.armAxis hd)) l =
      conjSpanCornerFarSite (Geometry.armAxis hd) (l + 1) := by
  rw [Path.advance_eq]
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [conjSpanCornerFarSite, step, SignedDirection.delta,
      SignedDirection.forward, unitVector]
    <;> omega
  · simp [conjSpanCornerFarSite, step, SignedDirection.delta,
      SignedDirection.forward, unitVector, hi]

theorem siteReflection_advance_zero_eq_conjSpanCornerOriginSite
    (hd : 3 ≤ d) (l : ℕ) :
    siteReflection (Geometry.armAxis hd) 0
        (Path.advance (0 : Site d) (.forward (Geometry.armAxis hd)) l) =
      conjSpanCornerOriginSite (Geometry.armAxis hd) l := by
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [Path.advance_eq, siteReflection, conjSpanCornerOriginSite,
      SignedDirection.delta_forward, unitVector]
  · simp [Path.advance_eq, siteReflection, conjSpanCornerOriginSite,
      SignedDirection.delta_forward, unitVector, hi]

theorem linkReflection_advance_step_zero_eq_conjSpanCornerOriginSite
    (hd : 3 ≤ d) (l : ℕ) :
    linkReflection (Geometry.armAxis hd) 0
        (Path.advance (step (0 : Site d) (.forward (Geometry.armAxis hd)))
          (.forward (Geometry.armAxis hd)) l) =
      conjSpanCornerOriginSite (Geometry.armAxis hd) l := by
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [Path.advance_eq, linkReflection, Lattice.Cubic.translate, step,
      conjSpanCornerOriginSite, SignedDirection.delta,
      SignedDirection.forward, unitVector]
  · simp [Path.advance_eq, linkReflection, Lattice.Cubic.translate, step,
      conjSpanCornerOriginSite, SignedDirection.delta,
      SignedDirection.forward, unitVector, hi]

/-- The reverse of the even site-reflected physical path, cast to the affine
square vertices. -/
def conjSpanEvenPhysicalArmPath (hd : 3 ≤ d) (l : ℕ) :
    Lattice.Cubic.Path
      (conjSpanCornerFarSite (Geometry.armAxis hd) l)
      (conjSpanCornerOriginSite (Geometry.armAxis hd) l) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (siteReflectedFullPath (Geometry.armAxis hd) 0 (0 : Site d)
        (conjSpanCornerZeroArm hd)
        (conjSpanSiteStraightHalfPath hd (0 : Site d) l)).reverse
      (advance_zero_forward_eq_conjSpanCornerFarSite hd l))
    (siteReflection_advance_zero_eq_conjSpanCornerOriginSite hd l)

/-- The reverse of the odd link-reflected physical path, cast to the affine
square vertices. -/
def conjSpanOddPhysicalArmPath (hd : 3 ≤ d) (l : ℕ) :
    Lattice.Cubic.Path
      (conjSpanCornerFarSite (Geometry.armAxis hd) (l + 1))
      (conjSpanCornerOriginSite (Geometry.armAxis hd) l) :=
  YangMills.Basic.OrientedPath.castTarget
    (YangMills.Basic.OrientedPath.castSource
      (reflectedFullPath (Geometry.armAxis hd) 0 (0 : Site d)
        (conjSpanCornerZeroArm hd)
        (straightPositiveHalfPath (Geometry.armAxis hd) (0 : Site d) l)).reverse
      (advance_step_zero_forward_eq_conjSpanCornerFarSite_succ hd l))
    (linkReflection_advance_step_zero_eq_conjSpanCornerOriginSite hd l)

theorem conjSpanEvenPhysicalArmPath_eq_cornerArm
    (hd : 3 ≤ d) (l : ℕ) :
    conjSpanEvenPhysicalArmPath hd l =
      conjSpanCornerArmToOrigin (Geometry.armAxis hd) l l := by
  apply Path.ext_directions
  simp [conjSpanEvenPhysicalArmPath, siteReflectedFullPath,
    siteReflectedMixedFullPath, siteReflectedIncomingPath,
    conjSpanSiteStraightHalfPath, SignedDirection.siteReflect,
    SignedDirection.forward, SignedDirection.backward,
    List.reverse_replicate, List.append_assoc]

theorem conjSpanOddPhysicalArmPath_eq_cornerArm
    (hd : 3 ≤ d) (l : ℕ) :
    conjSpanOddPhysicalArmPath hd l =
      conjSpanCornerArmToOrigin (Geometry.armAxis hd) l (l + 1) := by
  apply Path.ext_directions
  simp [conjSpanOddPhysicalArmPath, reflectedFullPath,
    reflectedIncomingPath, crossingThenPath, straightPositiveHalfPath,
    SignedDirection.siteReflect, SignedDirection.forward,
    SignedDirection.backward, List.reverse_replicate,
    List.replicate_succ, List.replicate_add, List.append_assoc,
    Nat.add_assoc]

/-! ## Exact pointwise connection to the physical-length family -/

theorem conjSpanEvenCornerFarEndpoint_apply_eq_siteEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    conjSpanCornerFarEndpoint hd sigma rho T l A =
      conjSpanSiteStraightEndpoint hd sigma rho T (0 : Site d) l A := rfl

theorem conjSpanOddCornerFarEndpoint_apply_eq_linkEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    conjSpanCornerFarEndpoint hd sigma rho T (l + 1) A =
      conjSpanLinkStraightEndpoint hd sigma rho T (0 : Site d) l A := by
  simp only [conjSpanCornerFarEndpoint, conjSpanLinkStraightEndpoint,
    LocalField.translatePullback_apply]
  congr 2
  ext i
  by_cases hi : i = Geometry.armAxis hd
  · subst i
    simp [unitVector]
  · simp [unitVector, hi]

/-- Reversing the affine odd straight segment gives exactly Task 3's
physical line of length `2*l+1`. -/
theorem conjSpanOddCornerStraight_reverse_apply_eq_physical
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    screenedObservable rho
        (conjSpanOddCornerOriginEndpoint hd sigma rho T l)
        (conjSpanCornerFarEndpoint hd sigma rho T (l + 1))
        (conjSpanCornerArmToOrigin (Geometry.armAxis hd) l (l + 1)).reverse A =
      conjSpanPhysicalStraightObservable hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l + 1) A := by
  rw [conjSpanPhysicalStraightObservable_odd]
  unfold conjSpanLinkStraightObservable
  rw [← conjSpanOddPhysicalArmPath_eq_cornerArm hd l]
  simp [conjSpanOddPhysicalArmPath, conjSpanOddCornerOriginEndpoint,
    screenedObservable_apply, screenedValue, holonomy_castSource,
    holonomy_castTarget, conjSpanOddCornerFarEndpoint_apply_eq_linkEndpoint]

/-! ## Pointwise normalization -/

/-- The even affine straight segment is the physical line of length
`2*l`, with the same normalized endpoint used at odd lengths. -/
theorem conjSpanEvenCornerStraight_reverse_apply_eq_physical
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    screenedObservable rho
        (conjSpanEvenCornerOriginEndpoint hd sigma rho T l)
        (conjSpanCornerFarEndpoint hd sigma rho T l)
        (conjSpanCornerArmToOrigin (Geometry.armAxis hd) l l).reverse A =
      conjSpanPhysicalStraightObservable hd sigma rho T (0 : Site d)
        (conjSpanCornerZeroArm hd) (2 * l) A := by
  rw [conjSpanPhysicalStraightObservable_even]
  unfold conjSpanSiteStraightObservable
  rw [← conjSpanEvenPhysicalArmPath_eq_cornerArm hd l]
  simp [conjSpanEvenPhysicalArmPath, conjSpanEvenCornerOriginEndpoint,
    siteReflectedObservable, siteReflectedMixedObservable, siteReflectedFullPath,
    screenedObservable_apply, screenedValue, holonomy_castSource,
    holonomy_castTarget, conjSpanEvenCornerFarEndpoint_apply_eq_siteEndpoint]

theorem conjSpanCornerFarEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (t : ℕ) (A : Configuration d G) :
    endpointL2Norm (conjSpanCornerFarEndpoint hd sigma rho T t A) ≤ 1 := by
  change endpointL2Norm (conjSpanPhi hd sigma rho T _ _) ≤ 1
  exact conjSpanPhi_l2Norm_le_one hd sigma rho T _ _

theorem conjSpanEvenCornerComparisonEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    endpointL2Norm
      (conjSpanEvenCornerComparisonEndpoint hd sigma rho T l A) ≤ 1 := by
  change endpointL2Norm (conjSpanCornerFarEndpoint hd sigma rho T l _) ≤ 1
  exact conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T l _

theorem conjSpanOddCornerComparisonEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (l : ℕ) (A : Configuration d G) :
    endpointL2Norm
      (conjSpanOddCornerComparisonEndpoint hd sigma rho T l A) ≤ 1 := by
  change endpointL2Norm
    (conjSpanCornerFarEndpoint hd sigma rho T (l + 1) _) ≤ 1
  exact conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T (l + 1) _

end

end YangMills.Gluelump.Propagation
