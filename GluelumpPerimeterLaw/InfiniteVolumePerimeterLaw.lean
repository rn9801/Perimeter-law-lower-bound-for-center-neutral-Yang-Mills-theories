/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLawStatement
import GluelumpPerimeterLaw.Propagation.CanonicalCofinalPerimeterLaw
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectationLimit
import GluelumpPerimeterLaw.Propagation.ConjSpanCornerExpectation
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightLimit

/-!
# Center-neutral gluelump perimeter law in the completed-box limit

This is the one-way application of the neutral gluelump propagation theorem
to a translation-invariant common local limit of the completed reflection
boxes.  Strong-coupling infrastructure is used only to supply that abstract
limit/reflection interface and the uniform positive one-link seed.
-/

namespace YangMills.Gluelump.InfiniteVolume

open MeasureTheory YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.StrongCoupling YangMills.Gluelump.Propagation
open YangMills.Gluelump.Endpoint YangMills.Gluelump.RepresentationTheory
open Representation

noncomputable section

universe u

variable {d n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The completed-free-boundary infinite-volume center-neutral perimeter law.

The screening degree, intertwiner, one-link base, and final rate are all
chosen before the limiting probability measure.  Consequently the rate is
uniform over every measure satisfying the common local-limit hypothesis. -/
theorem centerNeutralInfiniteVolumePerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) :
    CenterNeutralInfiniteVolumePerimeterLaw (d := d) sigma rho := by
  intro hd hsigma hcenter beta hbeta
  obtain ⟨m, Tmap, _hTmap, q, hq, huniform⟩ :=
    centerNeutral_exists_uniform_conjSpanPhysicalStraight_rate
      hd sigma hsigma rho hcenter (0 : Site d) rfl hbeta
  let g : ℝ := min q (1 / 2)
  have hg : 0 < g := lt_min hq (by norm_num)
  have hgq : g ≤ q := min_le_left q (1 / 2)
  have hgOne : g ≤ 1 :=
    (min_le_right q (1 / 2)).trans (by norm_num)
  let D : ℝ := r
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast rho.dimension_pos
  let B : ℝ := cofinalRectanglePowerBase m D g
  have hB : 0 < B := by
    unfold B cofinalRectanglePowerBase
    exact div_pos (pow_pos hg _) (zero_lt_one.trans_le hD)
  refine ⟨powerToExponentialRate B, powerToExponentialRate_pos hB, ?_⟩
  intro mu hmu x₀ a b R S hab hR hS
  let hstate : ReflectionPositiveState mu :=
    hmu.reflectionPositiveState sigma hbeta.le hd
  let hab₀ := Geometry.armAxis_ne_transverseAxis₁ hd
  let hrect : CanonicalRectangleExpectationCertificate mu rho hab₀ :=
    hmu.canonicalRectangleExpectationCertificate
      sigma hbeta.le hd rho hab₀
  let hswap : RectangleAxisSwapInvariant mu rho :=
    hmu.rectangleAxisSwapInvariant sigma hd rho
  let hcert : CofinalRectangleReflectionCertificate m D
      (conjSpanPhysicalStraightExpectation mu hd sigma rho Tmap
        (0 : Site d) (conjSpanCornerZeroArm hd))
      (conjSpanCornerBentExpectation mu hd sigma rho Tmap)
      (canonicalRectangleExpectation mu rho hab₀) := by
    simpa only [D] using
      conjSpanCofinalRectangleReflectionCertificate
        mu hstate hd sigma rho Tmap hrect
  have hline : ∀ length, 0 < length →
      g ^ length ≤ conjSpanPhysicalStraightExpectation
        mu hd sigma rho Tmap (0 : Site d)
          (conjSpanCornerZeroArm hd) length := by
    intro length hlength
    exact (pow_le_pow_left₀ hg.le hgq length).trans
      (huniform mu hmu hlength)
  have hpublic :=
    perimeterLaw_of_cofinalRectangleCertificate_fixedRate
      hstate rho hswap hab₀ hrect hcert hD hg hgOne hline
        x₀ a b R S hab hR hS
  simpa only [B, D, complexRectangleWilsonExpectation,
    rectangleWilsonExpectation, rectangleWilsonObservable,
    localExpectation] using hpublic

end

end YangMills.Gluelump.InfiniteVolume
