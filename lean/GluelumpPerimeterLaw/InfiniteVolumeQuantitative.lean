/-
Copyright (c) 2026 The Gluelump Perimeter Law Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Gluelump Perimeter Law contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLawStatement
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectationLimit
import GluelumpPerimeterLaw.Propagation.CanonicalRectanglePerimeter
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightLimit
import GluelumpPerimeterLaw.Propagation.PaperCorner
import GluelumpPerimeterLaw.OneLink.CouplingLowerBound

/-!
# A perimeter coefficient uniform over all positive couplings

The screening data are selected once. The explicit fixed-field seed then
gives one coefficient of `1 + beta + |log beta|`, simultaneously for every
positive coupling and every common ordinary-free-boundary limit. Coupling is stated
in the paper's unnormalized-character convention.
-/

namespace YangMills.Gluelump.InfiniteVolume

open MeasureTheory YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.StrongCoupling YangMills.Gluelump.Propagation
open YangMills.Gluelump.Endpoint YangMills.Gluelump.RepresentationTheory
open YangMills.Gluelump.OneLink Representation

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The screening tensor and final coefficient are chosen before the
coupling, measure and rectangle, as in the paper's main theorem. -/
theorem centerNeutralUniformCouplingPerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) :
    CenterNeutralUniformCouplingPerimeterLaw (d := d) sigma rho := by
  intro hd hsigma hcenter
  obtain ⟨m, Tmap, hTmap⟩ :=
    centerNeutral_exists_conjSpanIntertwiner sigma hsigma rho hcenter
  let x := step (0 : Site d) (.forward (Geometry.armAxis hd))
  let c := conjSpanOneLinkPaperCouplingConstant hd sigma rho Tmap hTmap x
  have hc : 0 < c :=
    conjSpanOneLinkPaperCouplingConstant_pos hd sigma rho Tmap hTmap x
  let C : ℝ := 2 * c + |Real.log (r : ℝ)| / 4
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro beta hbeta mu hmu x₀ a b R S hab hR hS
  have hn : (0 : ℝ) < n := by exact_mod_cast sigma.dimension_pos
  have hscaled : 0 < (n : ℝ) * beta := mul_pos hn hbeta
  let g := Real.exp (-c * couplingWeight beta)
  have hg : 0 < g := Real.exp_pos _
  have hseed : g ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho Tmap (0 : Site d) (conjSpanCornerZeroArm hd) 1 := by
    rw [conjSpanPhysicalStraightExpectation_one_eq]
    have hfinite := exp_neg_conjSpanOneLinkPaperCouplingConstant_le_lowerConstant
      hbeta hd sigma rho Tmap hTmap x
    have hlimit := conjSpanOneLinkLowerConstant_le_freeBoundaryLimit
      hd sigma rho Tmap hTmap (0 : Site d) rfl hscaled hmu
    exact hfinite.trans hlimit.1
  let hstate := hmu.reflectionPositiveState sigma hscaled.le hd
  let hab₀ := Geometry.armAxis_ne_transverseAxis₂ hd
  let hrect := hmu.canonicalRectangleExpectationCertificate
    sigma hscaled.le hd rho hab₀
  let hswap : RectangleAxisSwapInvariant mu rho :=
    hmu.rectangleAxisSwapInvariant sigma hd rho
  have hline : ∀ length, 0 < length →
      g ^ length ≤ conjSpanPhysicalStraightExpectation
        mu hd sigma rho Tmap (0 : Site d) (conjSpanCornerZeroArm hd) length := by
    intro length hlength
    exact hmu.conjSpanPhysicalStraightExpectation_rate_power_le
      hd sigma rho Tmap (0 : Site d) rfl hscaled.le hg hseed hlength
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast rho.dimension_pos
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans_le hr
  have hrectangle := paperRectangle_lower_bound_of_line_rate
    mu hstate hd sigma rho Tmap hrect hg hline hR hS
  have hweight := exp_neg_couplingWeight_rectangle_le_square
    hc.le hrpos hbeta.le (le_refl g) hR hS
  have hgeometry : canonicalRectangleExpectation mu rho hab₀ R S =
      (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
        ∂(mu : Measure (Configuration d G))).re := by
    unfold canonicalRectangleExpectation
    exact congrArg Complex.re
      (canonicalRectangleIntegral_eq_integral_rectangleBoundary
        hstate rho hswap hab₀ x₀ hab R S)
  have hbound := hweight.trans hrectangle
  rw [hgeometry] at hbound
  constructor
  · simpa only [complexRectangleWilsonExpectation, rectangleWilsonExpectation,
      rectangleWilsonObservable, localExpectation] using
      integral_rectangleBoundary_eq_re_of_canonical
        hstate rho hswap hab₀ hrect.reality x₀ hab R S
  · simpa only [C, couplingWeight, complexRectangleWilsonExpectation,
      rectangleWilsonExpectation, rectangleWilsonObservable, localExpectation] using
      hbound

end

end YangMills.Gluelump.InfiniteVolume
