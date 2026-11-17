/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflectionBridge
import YangMills.Gauge.LinkReflectionBridge

/-! Additive evaluation identity for the link-reflection finite bridge. -/

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- A labelled strict-positive edge is read back unchanged by the one-sided
evaluation map. -/
@[simp]
theorem linkEvaluateSide_apply_of_mem
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (U : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (e : PositiveEdge d) (he : e ∈ Λ.linkPositiveEdges τ k) :
    Λ.linkEvaluateSide τ k hΛ U e = U ⟨e, he⟩ := by
  have hedyn : e ∈ Λ.dynamicEdges := (Finset.mem_filter.mp he).1
  rw [linkEvaluateSide, ContinuousMap.comp_apply, linkEvaluatePositive,
    ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  change Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, U))) e = U ⟨e, he⟩
  rw [Λ.evaluate_of_mem _ e hedyn]
  let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
  have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
      Sum.inr (Sum.inr (⟨e, he⟩ : Λ.linkPositiveEdges τ k)) := by
    unfold linkEdgeLabelEquiv
    dsimp [edyn]
    rw [dif_neg, dif_pos he]
    intro hc
    have hsource := (Finset.mem_filter.mp he).2
    have hcross := (Finset.mem_filter.mp hc).2.2
    omega
  simp only [linkAssemble, ContinuousMap.coe_mk]
  rw [hlabel]

end FiniteSpecification

end


end YangMills.Gauge
