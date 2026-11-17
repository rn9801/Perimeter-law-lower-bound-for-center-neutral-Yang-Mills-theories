/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.StrongCouplingPerimeterLaw

/-! Regression checks for the one-way strong-coupling perimeter-law adapter. -/

#check YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw

namespace YangMills.Tests.GluelumpStrongCouplingPerimeterLaw

open MeasureTheory YangMills.Gauge YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

variable (sigma : ContinuousUnitaryRepData G n)
  (rho : ContinuousUnitaryRepData G r)

/- Regression guard: the concrete strong-coupling corollary applies without
an irreducibility argument. -/
#check fun (hd : 3 ≤ d) (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbetaPos : 0 < beta) =>
  YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw
    (d := d) sigma rho hd hsigma hcenter beta hbetaPos

end

end YangMills.Tests.GluelumpStrongCouplingPerimeterLaw

#print axioms
  YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw
