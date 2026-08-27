/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcreteOneLinkLowerBound
import GluelumpPerimeterLaw.RepresentationTheory.CenterScreening

/-!
# Center-neutral uniform one-link lower bound

Center neutrality supplies one fixed nonzero conjugation-span screening
intertwiner.  The concrete one-link estimate then supplies one strictly
positive constant, uniform over every finite specification satisfying the
explicit reflection, collar, visibility, and support conditions below.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint
open RepresentationTheory Representation

noncomputable section

universe u

variable {d n r m : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  [Measure.IsOpenPosMeasure (GaugeHaarProbability.haar G)]

/-- The exact finite-volume conditions used by the direct one-link proof.
Keeping these conditions visible avoids folding geometric admissibility into
an opaque positivity assumption. -/
structure ConjSpanOneLinkAdmissible
    (Lambda : FiniteSpecification d G) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) : Prop where
  linkSymmetric : Lambda.LinkSymmetric (Geometry.armAxis hd) 0
  plaquetteClosed : Lambda.PlaquetteClosed
  collar : combEndpointCollar (m := m) hd
      (step z (.forward (Geometry.armAxis hd))) ⊆
    Lambda.linkPositiveEdges (Geometry.armAxis hd) 0
  visible : ∀ e ∈ combEndpointCollar (m := m) hd
      (step z (.forward (Geometry.armAxis hd))),
    ∃ p : Lambda.linkCrossPlaquettes (Geometry.armAxis hd) 0,
      FiniteSpecification.linkCrossPositiveEdge (Geometry.armAxis hd) p.1 = e
  dynamicSupport :
    (conjSpanReflectedOneLinkObservable hd sigma rho T z hz).support ⊆
      Lambda.dynamicEdges

/-- The concrete estimate in bundled-admissibility form. -/
theorem ConjSpanOneLinkAdmissible.lowerBound
    (Lambda : FiniteSpecification d G) (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hT : T ≠ 0) (z : Site d)
    (hz : z (Geometry.armAxis hd) = 0)
    (hLambda : ConjSpanOneLinkAdmissible Lambda hd sigma rho T z hz)
    {beta : ℝ} (hbeta : 0 < beta) :
    conjSpanOneLinkLowerConstant beta hd sigma rho T hT
        (step z (.forward (Geometry.armAxis hd))) ≤
      Complex.re (∫ A,
        conjSpanReflectedOneLinkObservable hd sigma rho T z hz
          (Lambda.evaluate A)
        ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) :=
  conjSpanOneLinkLowerConstant_le_gibbsExpectation
    Lambda hd hLambda.linkSymmetric hLambda.plaquetteClosed sigma rho T hT
      z hz hLambda.collar hLambda.visible hLambda.dynamicSupport hbeta

/-- Operational center-neutral one-link package: one screening tensor power,
one nonzero intertwiner, and one positive number work for every admissible
finite specification. -/
theorem centerNeutral_exists_uniform_conjSpanOneLink_lowerBound
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (rho : ContinuousUnitaryRepData G r)
    (hcenter : CenterNeutral (asRepresentation rho))
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
        (tensorPower (conjSpanRep sigma) m) (asRepresentation rho),
      T ≠ 0 ∧ ∃ q : ℝ, 0 < q ∧
        ∀ (Lambda : FiniteSpecification d G),
          ConjSpanOneLinkAdmissible Lambda hd sigma rho T z hz →
          q ≤ Complex.re (∫ A,
            conjSpanReflectedOneLinkObservable hd sigma rho T z hz
              (Lambda.evaluate A)
            ∂FiniteVolume.gibbsMeasure Lambda sigma.wilsonPotential beta) := by
  obtain ⟨m, T, hT⟩ :=
    centerNeutral_exists_conjSpanIntertwiner sigma hsigma rho hcenter
  let q := conjSpanOneLinkLowerConstant beta hd sigma rho T hT
    (step z (.forward (Geometry.armAxis hd)))
  refine ⟨m, T, hT, q, ?_, ?_⟩
  · exact conjSpanOneLinkLowerConstant_pos hbeta hd sigma rho T hT _
  · intro Lambda hLambda
    exact ConjSpanOneLinkAdmissible.lowerBound
      Lambda hd sigma rho T hT z hz hLambda hbeta

end

end YangMills.Gluelump.OneLink
