/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.StrictPositivity
import GluelumpPerimeterLaw.Upstream.StrongCoupling.ConcreteLinkReflectionPositivity

/-!
# Strict one-link positivity along the completed exhaustion

This file specializes the finite-volume transverse-prism detector to the
completed link-symmetric boxes used to construct the infinite-volume state.
Only the finitely many prisms incident to the endpoint collar are required;
no finite specification is asked to contain every plaquette in the cutting
plane.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint
open StrongCoupling Filter Set Propagation
open scoped Matrix Topology

noncomputable section

local instance exhaustionStrictDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d m n N nsigma : ℕ} {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- A transverse collar contained in the internal edge set of a completed
link-symmetric box is visible through actual cross-plane plaquettes.  Each
such plaquette is active because it is incident to its selected collar edge. -/
theorem transverseLoop_support_has_linkCrossPlaquette_of_box
    (hd : 3 ≤ d) (x : Site d) (k : ℤ)
    (hx : x (Geometry.armAxis hd) = k + 1) (boxRadius : ℕ)
    (hbox : basedLoopSupport (transverseLoop (m := m) hd x) ⊆
      (linkSymmetricBox d boxRadius (Geometry.armAxis hd)).positiveEdges) :
    ∀ e ∈ basedLoopSupport (transverseLoop (m := m) hd x),
      ∃ p : (linkSymmetricSpecification G d boxRadius
          (Geometry.armAxis hd)).linkCrossPlaquettes
            (Geometry.armAxis hd) k,
        FiniteSpecification.linkCrossPositiveEdge
          (Geometry.armAxis hd) p.1 = e := by
  intro e he
  obtain ⟨p, hpbase, hpperp, hpedge, hpboundary⟩ :=
    transverseLoop_support_has_prismPlaquette hd x e he
  have hpbase' : p.base (Geometry.armAxis hd) = k := by
    rw [hpbase, hx]
    omega
  have hpactive : p ∈
      (linkSymmetricSpecification G d boxRadius
        (Geometry.armAxis hd)).activePlaquettes := by
    change p ∈ linkSymmetricActivePlaquettes d boxRadius
      (Geometry.armAxis hd)
    rw [linkSymmetricActivePlaquettes, Finset.mem_biUnion]
    exact ⟨e, hbox he,
      mem_incidentPlaquettes_of_mem_boundary e p hpboundary⟩
  exact ⟨⟨p, Finset.mem_filter.mpr
    ⟨hpactive, hpbase', hpperp⟩⟩, hpedge⟩

/-- The completed link-symmetric exhaustion eventually satisfies every
finite-volume hypothesis of the strict transverse one-link theorem. -/
theorem eventually_transverseOneLink_linkSymmetric_finite_strict
    [MeasureTheory.Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G nsigma)
    (hfaithful : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      representationAction rho h (T v))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    (hendpoint : ∃ u : Fin m → G,
      T (fun j => Lie.axialMatrix eta (u j)) ≠ 0) :
    ∃ boxRadius0, ∀ boxRadius, boxRadius0 ≤ boxRadius →
      ∀ᶠ beta in 𝓝[>] (0 : ℝ),
        0 < Complex.re
          (∫ A, transverseStraightArmObservable hd rho eta T z hz 0
              ((linkSymmetricSpecification G d boxRadius
                (Geometry.armAxis hd)).evaluate A)
            ∂FiniteVolume.gibbsMeasure
              (linkSymmetricSpecification G d boxRadius
                (Geometry.armAxis hd))
              sigma.wilsonPotential beta) := by
  let tau := Geometry.armAxis hd
  let x := step z (.forward tau)
  let O := transverseStraightArmObservable hd rho eta T z hz 0
  let collar := basedLoopSupport (transverseLoop (m := m) hd x)
  obtain ⟨observableRadius, hobservable⟩ :=
    finiteSupport_subset_linkSymmetricBox tau O.support
  obtain ⟨collarRadius, hcollar⟩ :=
    finiteSupport_subset_linkSymmetricBox tau collar
  refine ⟨max observableRadius collarRadius, fun boxRadius hRadius => ?_⟩
  let Λ := linkSymmetricSpecification G d boxRadius tau
  have hobservableBox : O.support ⊆
      (linkSymmetricBox d boxRadius tau).positiveEdges :=
    hobservable.trans (linkSymmetricBox_positiveEdges_mono
      ((Nat.le_max_left observableRadius collarRadius).trans hRadius) tau)
  have hcollarBox : collar ⊆
      (linkSymmetricBox d boxRadius tau).positiveEdges :=
    hcollar.trans (linkSymmetricBox_positiveEdges_mono
      ((Nat.le_max_right observableRadius collarRadius).trans hRadius) tau)
  have hobservableDyn : O.support ⊆ Λ.dynamicEdges := by
    intro e he
    exact Finset.mem_union_left _ (hobservableBox he)
  have hcollarDyn : collar ⊆ Λ.dynamicEdges := by
    intro e he
    exact Finset.mem_union_left _ (hcollarBox he)
  apply eventually_transverseOneLink_finite_strict Λ hd
    (linkSymmetricSpecification_linkSymmetric boxRadius tau)
    (linkSymmetricSpecification_plaquetteClosed boxRadius tau)
    sigma hfaithful rho eta T hT z hz
  · simpa [O] using hobservableDyn
  · exact hendpoint
  · simpa [collar, x, tau] using hcollarDyn
  · refine transverseLoop_support_has_linkCrossPlaquette_of_box
      (G := G) hd x 0 ?_ boxRadius ?_
    · simp [x, tau, step, SignedDirection.forward,
        SignedDirection.delta, unitVector, hz]
    · simpa [collar, tau] using hcollarBox

end

end YangMills.Gluelump.OneLink
