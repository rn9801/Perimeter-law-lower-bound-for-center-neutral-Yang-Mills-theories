/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteVolume

/-! Additive finite-volume continuity lemma used by the gluelump package. -/

open MeasureTheory

namespace YangMills.Gauge.FiniteVolume

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The finite-volume partition function varies continuously with the real
coupling. -/
theorem continuous_partitionFunction
    [CompactSpace G]
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    Continuous fun β : ℝ => partitionFunction Λ Φ β := by
  unfold partitionFunction boltzmannWeight
  have h := continuous_parametric_integral_of_continuous
    (μ := Λ.haarMeasure)
    (s := Set.univ)
    (f := fun β : ℝ => fun U : DynamicConfiguration Λ =>
      Real.exp (β * action Λ Φ U))
    (by
      exact Real.continuous_exp.comp
        (continuous_fst.mul
          ((continuous_action Λ Φ).comp continuous_snd)))
    isCompact_univ
  simpa using h

end

end YangMills.Gauge.FiniteVolume
