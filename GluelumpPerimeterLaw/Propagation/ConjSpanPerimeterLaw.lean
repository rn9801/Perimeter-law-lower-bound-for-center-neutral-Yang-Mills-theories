/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalCofinalPerimeterLaw
import GluelumpPerimeterLaw.Propagation.ConjSpanCornerExpectation
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightExpectation

/-!
# Neutral direct-field gluelump perimeter law

This is the theorem intended for the future standalone gluelump repository.
It assumes only a neutral reflection-positive state, the two gauge-fixed
crossing-link callback packages, coordinate-swap invariance, and positivity
of the direct one-bond screened observable.  It contains no finite-volume
exhaustion, cluster expansion, or strong-coupling-radius hypothesis.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson Endpoint OneLink
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [YangMills.Gauge.GaugeHaarProbability G]

/-- A positive direct one-link seed, together with the neutral reflection
interfaces, implies the full real perimeter-law lower bound. -/
theorem conjSpanPerimeterLaw_of_positiveOneLink
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (hlineLink : ConjSpanLinkReflectionData mu hd sigma rho T
      (0 : Site d) (conjSpanCornerZeroArm hd))
    (hrectangleLink : CanonicalRectangleLinkReflectionData mu rho
      (Geometry.armAxis_ne_transverseAxis₁ hd))
    (hswap : RectangleAxisSwapInvariant mu rho)
    {q : ℝ} (hq : 0 < q) (hqOne : q ≤ 1)
    (hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd) 1) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (x₀ : Site d) (a b : Fin d) (R S : ℕ),
        a ≠ b → 0 < R → 0 < S →
          (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
              ∂(mu : Measure (Configuration d G))) =
              ((∫ A, rho.wilsonLoop
                (Path.rectangleBoundary x₀ a b R S) A
                  ∂(mu : Measure (Configuration d G))).re : ℂ) ∧
            Real.exp (-rate * ((2 * (R + S) : ℕ) : ℝ)) ≤
              (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
                ∂(mu : Measure (Configuration d G))).re := by
  let hab := Geometry.armAxis_ne_transverseAxis₁ hd
  let line : ℕ → ℝ := fun length =>
    conjSpanPhysicalStraightExpectation mu hd sigma rho T (0 : Site d)
      (conjSpanCornerZeroArm hd) length
  let bent : ℕ → ℝ := fun length =>
    conjSpanCornerBentExpectation mu hd sigma rho T length
  have hrect : CanonicalRectangleExpectationCertificate mu rho hab :=
    canonicalRectangleExpectationCertificate
      (mu := mu) (rho := rho) (hab := hab)
      hstate hrectangleLink hswap
  have hbend : ∀ length, m ≤ length → Odd length →
      line length ^ 2 ≤ bent length := by
    intro length hm hodd
    obtain ⟨l, rfl⟩ := hodd
    exact conjSpanPhysicalStraightExpectation_sq_le_cornerBent_odd
      mu hstate hd sigma rho T l hm
  have hclose : ∀ length, m ≤ length → Odd length →
      bent length ^ 2 / (r : ℝ) ≤
        canonicalRectangleExpectation mu rho hab length length := by
    intro length _hm hodd
    obtain ⟨l, rfl⟩ := hodd
    exact (conjSpanCornerBent_sq_div_dimension_le_square_odd
      mu hstate hd sigma rho T l).trans_eq
        (conjSpanCornerSquareExpectation_eq_canonicalRectangleExpectation_odd
          mu hstate rho hab l)
  have hcert : CofinalRectangleReflectionCertificate m (r : ℝ)
      line bent (canonicalRectangleExpectation mu rho hab) :=
    hrect.toCofinal hbend hclose
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast rho.dimension_pos
  have hline : ∀ length, 0 < length → q ^ length ≤ line length := by
    intro length hlength
    exact conjSpanPhysicalStraightExpectation_rate_power_le
      mu hstate hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd)
      hlineLink hq hqseed hlength
  exact perimeterLaw_of_cofinalRectangleCertificate
    hstate rho hswap hab hrect hcert hr hq hqOne hline

end

end YangMills.Gluelump.Propagation
