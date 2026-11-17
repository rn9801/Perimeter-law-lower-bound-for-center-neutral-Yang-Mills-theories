/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflection
import YangMills.Gauge.SiteReflectionPositivity

/-! Additive measure invariance for the site-reflection normal form. -/

open MeasureTheory

namespace YangMills.Gauge.SiteReflection

noncomputable section

variable {G P O : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] [Fintype P] [Fintype O]

omit [TopologicalSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] in
/-- Swapping the two strict half-volume fields preserves reflected product
Haar measure. -/
theorem measurePreserving_reflect :
    MeasurePreserving
      (WilsonActionDecomposition.reflect : ReflectedConfiguration G P O →
        ReflectedConfiguration G P O)
      reflectedHaar reflectedHaar := by
  have hswap : MeasurePreserving
      (Prod.swap : SideConfiguration G P × SideConfiguration G P →
        SideConfiguration G P × SideConfiguration G P)
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) :=
    Measure.measurePreserving_swap
  simpa only [WilsonActionDecomposition.reflect] using
    MeasurePreserving.prod
      (MeasurePreserving.id (planeHaar (G := G) (O := O))) hswap

end


end YangMills.Gauge.SiteReflection
