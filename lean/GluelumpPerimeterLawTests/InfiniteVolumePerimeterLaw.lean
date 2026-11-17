/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLawTests.NeutralCriticalPath
import GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw
import GluelumpPerimeterLaw.Propagation.ConjSpanPerimeterLaw

/-!
# Regression checks for the center-neutral infinite-volume perimeter law

These checks pin both the model-neutral direct-field assembly theorem and its
paper-convention infinite-volume application.
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

variable (sigma : ContinuousUnitaryRepData G n)
  (rho : ContinuousUnitaryRepData G r)

/- Regression guard: one C is selected before beta and mu, with no
irreducibility or small-coupling hypothesis. The finite law is the paper's. -/
example (hd : 3 ≤ d) (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho)) :
    ∃ C : ℝ, 0 < C ∧ ∀ beta : ℝ, 0 < beta →
      ∀ mu : ProbabilityMeasure (YangMills.Gauge.Configuration d G),
        YangMills.StrongCoupling.IsTranslationInvariantPaperFreeBoundaryLimit sigma beta mu →
        ∀ (x0 : YangMills.Lattice.Cubic.Site d) (a b : Fin d) (R T : ℕ),
          a ≠ b → 0 < R → 0 < T →
          YangMills.Gluelump.InfiniteVolume.complexRectangleWilsonExpectation
              mu rho x0 a b R T =
            (YangMills.Gluelump.InfiniteVolume.rectangleWilsonExpectation
              mu rho x0 a b R T : ℂ) ∧
          Real.exp (-C * (1 + beta + |Real.log beta|) * (2 * (R + T) : ℕ)) ≤
            YangMills.Gluelump.InfiniteVolume.rectangleWilsonExpectation
              mu rho x0 a b R T :=
  YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
    sigma rho hd hsigma hcenter

#check YangMills.Gluelump.Propagation.paperPhysicalStraightExpectation_sq_le_cornerBent
#check YangMills.Gluelump.Propagation.paperCornerBent_sq_div_dimension_le_square
#check YangMills.Gluelump.Propagation.paperRectangle_lower_bound_of_line_rate

end

end YangMills.Tests.GluelumpInfiniteVolumePerimeterLaw

#print axioms YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
#print axioms YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw

assert_only_standard_axioms
  YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
assert_only_standard_axioms
  YangMills.Gluelump.OneLink.conjSpanOneLinkLowerConstant_eq_monomial_exp
