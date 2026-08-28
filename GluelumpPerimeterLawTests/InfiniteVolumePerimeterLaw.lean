/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw
import GluelumpPerimeterLaw.Propagation.ConjSpanPerimeterLaw

/-!
# Regression checks for the center-neutral infinite-volume perimeter law

These checks pin both the model-neutral direct-field assembly theorem and its
completed-free-boundary strong-coupling application.
-/

#check YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
#check YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw

namespace YangMills.Tests.GluelumpInfiniteVolumePerimeterLaw

open MeasureTheory YangMills.Gauge YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

variable (sigma : ContinuousUnitaryRepData G n)
  (rho : ContinuousUnitaryRepData G r)

/- Regression guard: the proved headline theorem applies without an
irreducibility argument. -/
#check fun (hd : 3 ≤ d) (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbeta : 0 < beta) =>
  YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
    (d := d) sigma rho hd hsigma hcenter beta hbeta

end

end YangMills.Tests.GluelumpInfiniteVolumePerimeterLaw

#print axioms YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
#print axioms YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
