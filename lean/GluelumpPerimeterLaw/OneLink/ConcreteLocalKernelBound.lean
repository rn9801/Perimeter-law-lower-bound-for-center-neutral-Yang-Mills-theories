/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcretePartitionFunction
import GluelumpPerimeterLaw.OneLink.ConjugationSpanBoundaryMode
import GluelumpPerimeterLaw.OneLink.LocalIncidence

/-!
# A volume-independent endpoint-kernel bound

Selected crossing labels are kept as plaquette labels: several crossing
plaquettes may read the same collar edge.  Sending a selected label to its
underlying plaquette embeds the full label subtype into the active
plaquettes meeting the fixed physical comb collar.  The existing cubic
incidence estimate therefore bounds the number of labels uniformly in the
finite specification.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson

noncomputable section

universe u

variable {d m n : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The number of selected crossing-plaquette labels is controlled by the
fixed comb collar, independently of the ambient finite specification.
Repeated labels over one physical collar edge remain distinct. -/
theorem card_linkCombSelectedCrossingLabels_le
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n) :
    Fintype.card
        {q : Lambda.linkCrossPlaquettes tau k //
          linkCombSelected (m := m) Lambda tau k hd x
            ((FiniteSpecification.linkCoordinateCrossingData
              Lambda tau k hLambda hclosed sigma).edge q)} ≤
      4 * d * (combEndpointCollar (m := m) hd x).card := by
  let E := combEndpointCollar (m := m) hd x
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  let labels := {q : Lambda.linkCrossPlaquettes tau k // selected (data.edge q)}
  let target := ↥(plaquettesMeetingEdges Lambda.activePlaquettes E)
  let f : labels → target := fun q ↦ by
    refine ⟨q.1.1, ?_⟩
    rw [mem_plaquettesMeetingEdges]
    refine ⟨(Finset.mem_filter.mp q.1.2).1, ?_⟩
    rw [Finset.not_disjoint_iff]
    refine ⟨FiniteSpecification.linkCrossPositiveEdge tau q.1.1, ?_, ?_⟩
    · exact FiniteSpecification.linkCrossPositiveEdge_mem_boundary tau q.1.1
        (Finset.mem_filter.mp q.1.2).2.2
    · exact q.2
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : target ↦ z.1) hq
  calc
    Fintype.card labels ≤ Fintype.card target :=
      Fintype.card_le_of_injective f hf
    _ = (plaquettesMeetingEdges Lambda.activePlaquettes E).card :=
      Fintype.card_coe _
    _ ≤ 4 * d * E.card :=
      card_plaquettesMeetingEdges_le Lambda.activePlaquettes E

/-- A manifestly volume-independent upper constant for the selected
endpoint exponential kernel. -/
def linkCombLocalKernelBound
    (beta : ℝ) (hd : 3 ≤ d) (x : Site d) (n : ℕ) : ℝ :=
  Real.exp ((beta / (2 * n)) *
    (2 * n * (4 * d * (combEndpointCollar (m := m) hd x).card)))

theorem linkCombLocalKernelBound_pos
    (beta : ℝ) (hd : 3 ≤ d) (x : Site d) (n : ℕ) :
    0 < linkCombLocalKernelBound (m := m) beta hd x n := by
  exact Real.exp_pos _

/-- The concrete selected endpoint kernel is bounded by the fixed-collar
constant in every ambient finite specification. -/
theorem realExpFeatureKernel_linkCombEndpointFeature_le
    (Lambda : FiniteSpecification d G) (tau : Fin d) (k : ℤ)
    (hLambda : Lambda.LinkSymmetric tau k)
    (hclosed : Lambda.PlaquetteClosed)
    (hd : 3 ≤ d) (x : Site d)
    (sigma : ContinuousUnitaryRepData G n)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (z : (CollarCoordinate
      (linkCombSelected (m := m) Lambda tau k hd x) → G) ×
      (CollarCoordinate
        (linkCombSelected (m := m) Lambda tau k hd x) → G)) :
    realExpFeatureKernel (beta / (2 * n))
        ((FiniteSpecification.linkCoordinateCrossingData
          Lambda tau k hLambda hclosed sigma).endpointFeature
          (linkCombSelected (m := m) Lambda tau k hd x)) z ≤
      linkCombLocalKernelBound (m := m) beta hd x n := by
  let data := FiniteSpecification.linkCoordinateCrossingData
    Lambda tau k hLambda hclosed sigma
  let selected := linkCombSelected (m := m) Lambda tau k hd x
  have halpha : 0 ≤ beta / (2 * n : ℝ) := by positivity
  apply (data.realExpFeatureKernel_endpointFeature_le
    selected halpha z).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left
  · have hcard := card_linkCombSelectedCrossingLabels_le
      (m := m) Lambda tau k hLambda hclosed hd x sigma
    exact_mod_cast Nat.mul_le_mul_left (2 * n) hcard
  · positivity

end

end YangMills.Gluelump.OneLink
