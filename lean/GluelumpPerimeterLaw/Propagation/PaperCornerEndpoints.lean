/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ConjSpanCornerEndpoints

/-!
# Endpoint placement for the paper's rectangle plane

The arm and the short comb direction span the rectangle plane. The long
comb direction is transverse to that plane, so a positive arm length always
suffices for bending, independently of the screening degree.
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

theorem paperCornerFarEndpoint_support_coordinates
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (t : ℕ) {e : PositiveEdge d}
    (he : e ∈ (conjSpanCornerFarEndpoint hd sigma rho T t).support) :
    e.source (Geometry.armAxis hd) = t ∧ e.target (Geometry.armAxis hd) = t ∧
      0 ≤ e.source (Geometry.transverseAxis₂ hd) ∧
      e.source (Geometry.transverseAxis₂ hd) ≤ 1 ∧
      0 ≤ e.target (Geometry.transverseAxis₂ hd) ∧
      e.target (Geometry.transverseAxis₂ hd) ≤ 1 := by
  change e ∈ (conjSpanStraightBaseEndpoint hd sigma rho T (0 : Site d)).support.image
    (PositiveEdge.translate (((t : ℤ) - 1) • unitVector (Geometry.armAxis hd))) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  change e₀ ∈ (conjSpanPhi hd sigma rho T
    (step (0 : Site d) (.forward (Geometry.armAxis hd)))).support at he₀
  rw [conjSpanPhi_support] at he₀
  have harm := basedLoopSupport_combLoops_armPlane hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  have hshort := basedLoopSupport_combLoops_transverseAxis₂_bounds hd
    (step (0 : Site d) (.forward (Geometry.armAxis hd))) e₀ he₀
  simp [PositiveEdge.source_translate, PositiveEdge.target_translate,
    Lattice.Cubic.translate, step, SignedDirection.forward,
    SignedDirection.delta, unitVector, Geometry.armAxis_ne_transverseAxis₂ hd,
    (Geometry.armAxis_ne_transverseAxis₂ hd).symm] at harm hshort ⊢
  omega

theorem paperCornerFarEndpoint_supportedInDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (s t : ℕ) (hpositive : 1 ≤ s + t) :
    (conjSpanCornerFarEndpoint hd sigma rho T t).SupportedInDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(s : ℤ)) := by
  intro e he
  have hc := paperCornerFarEndpoint_support_coordinates hd sigma rho T t he
  omega

theorem paperCornerFarEndpoint_supportedInAntiDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (t : ℕ) :
    (conjSpanCornerFarEndpoint hd sigma rho T t).SupportedInAntiDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) t := by
  intro e he
  have hc := paperCornerFarEndpoint_support_coordinates hd sigma rho T t he
  omega

theorem paperCornerFarEndpoint_diagonalPullback_supportedInAntiDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (s t : ℕ) :
    Endpoint.LocalField.SupportedInAntiDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) t
      ((conjSpanCornerFarEndpoint hd sigma rho T t).diagonalPullback
        (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(s : ℤ))) := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  have hc := paperCornerFarEndpoint_support_coordinates hd sigma rho T t he₀
  have hab := Geometry.armAxis_ne_transverseAxis₂ hd
  simp [PositiveEdge.source_diagonalReflect, PositiveEdge.target_diagonalReflect,
    diagonalReflection, hab, hab.symm] at hc ⊢
  omega

def paperOddCornerComparisonEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanOddCornerOriginEndpoint hd sigma rho T l).diagonalPullback
    (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(l : ℤ))

def paperEvenCornerComparisonEndpoint
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) : LocalField d G (Fin r → ℂ) :=
  (conjSpanEvenCornerOriginEndpoint hd sigma rho T l).diagonalPullback
    (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(l : ℤ))

theorem paperOddCornerComparisonEndpoint_supportedInDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) :
    (paperOddCornerComparisonEndpoint hd sigma rho T l).SupportedInDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(l : ℤ)) := by
  have hab := Geometry.armAxis_ne_transverseAxis₂ hd
  intro e he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  rcases Finset.mem_image.mp he₀ with ⟨e₁, he₁, rfl⟩
  have hc := paperCornerFarEndpoint_support_coordinates hd sigma rho T (l + 1) he₁
  rcases PositiveEdge.linkReflect_endpoints (Geometry.armAxis hd) 0 e₁ with h | h
  all_goals
    rw [PositiveEdge.source_diagonalReflect, PositiveEdge.target_diagonalReflect hab,
      h.1, h.2]
    simp [diagonalReflection, linkReflection, siteReflection,
      Lattice.Cubic.translate, unitVector, hab, hab.symm] at hc ⊢
    omega

theorem paperEvenCornerComparisonEndpoint_supportedInDiagonalPositiveHalf
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) :
    (paperEvenCornerComparisonEndpoint hd sigma rho T l).SupportedInDiagonalPositiveHalf
      (Geometry.armAxis hd) (Geometry.transverseAxis₂ hd) (-(l : ℤ)) := by
  have hab := Geometry.armAxis_ne_transverseAxis₂ hd
  intro e he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  rcases Finset.mem_image.mp he₀ with ⟨e₁, he₁, rfl⟩
  have hc := paperCornerFarEndpoint_support_coordinates hd sigma rho T l he₁
  rcases PositiveEdge.siteReflect_endpoints (Geometry.armAxis hd) 0 e₁ with h | h
  all_goals
    rw [PositiveEdge.source_diagonalReflect, PositiveEdge.target_diagonalReflect hab,
      h.1, h.2]
    simp [diagonalReflection, siteReflection, unitVector, hab, hab.symm] at hc ⊢
    omega

theorem paperOddCornerComparisonEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) (A : Configuration d G) :
    endpointL2Norm (paperOddCornerComparisonEndpoint hd sigma rho T l A) ≤ 1 := by
  change endpointL2Norm (conjSpanCornerFarEndpoint hd sigma rho T (l + 1) _) ≤ 1
  exact conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T (l + 1) _

theorem paperEvenCornerComparisonEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho)) (l : ℕ) (A : Configuration d G) :
    endpointL2Norm (paperEvenCornerComparisonEndpoint hd sigma rho T l A) ≤ 1 := by
  change endpointL2Norm (conjSpanCornerFarEndpoint hd sigma rho T l _) ≤ 1
  exact conjSpanCornerFarEndpoint_l2Norm_le_one hd sigma rho T l _

end

end YangMills.Gluelump.Propagation
