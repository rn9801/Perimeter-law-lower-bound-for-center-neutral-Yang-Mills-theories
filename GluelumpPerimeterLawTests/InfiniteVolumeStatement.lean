/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLawStatement

/-! Axiom regression for the free-boundary infinite-volume hypothesis. -/

open YangMills
open MeasureTheory YangMills.Gauge YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/- Regression guard: full support of the selected normalized Haar probability
is synthesized from the ambient compact-group hypotheses, not assumed. -/
#synth Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)

variable (sigma : ContinuousUnitaryRepData G n)
  (rho : ContinuousUnitaryRepData G r)

/- Regression guard: the public proposition requires center neutrality but
not irreducibility of the Wilson representation. -/
#check fun
    (hmain : Gluelump.InfiniteVolume.CenterNeutralInfiniteVolumePerimeterLaw
      (d := d) sigma rho)
    (hd : 3 ≤ d) (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbeta : 0 < beta) =>
  hmain hd hsigma hcenter beta hbeta

end

#print axioms
  StrongCoupling.wilsonStrongCoupling_isTranslationInvariantFreeBoundaryLimit
#print axioms
  Gluelump.InfiniteVolume.CenterNeutralInfiniteVolumePerimeterLaw
