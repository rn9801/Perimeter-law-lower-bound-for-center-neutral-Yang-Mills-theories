/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.RepresentationTheory.DualIrreducible
import GluelumpPerimeterLaw.RepresentationTheory.DualUnitary
import GluelumpPerimeterLaw.RepresentationTheory.TensorGeneration
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Center-neutral screening by the literal conjugation span
-/

namespace YangMills.Gluelump.RepresentationTheory

open MeasureTheory Representation YangMills.Gauge YangMills.Wilson
open scoped Matrix TensorProduct

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  {n p : ℕ}

/-- Center neutrality produces the operational nonzero map from a tensor
power of the literal conjugation span to the algebraic dual Wilson
representation. -/
theorem centerNeutral_exists_conjSpanIntertwiner
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (tau : ContinuousUnitaryRepData G p)
    (hcenter : CenterNeutral (asRepresentation tau)) :
    ∃ m : ℕ, ∃ T : IntertwiningMap
      (tensorPower (conjSpanRep sigma) m) (asRepresentation tau).dual,
      T ≠ 0 := by
  let Q := G ⧸ Subgroup.center G
  letI : IsClosed (Subgroup.center G : Set G) := isClosed_center
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  letI : GaugeHaarProbability Q := GaugeHaarProbability.ofCompact Q
  let source := conjSpanCenterQuotientUnitaryRepData sigma hsigma
  let dualTau := dualUnitaryRepData tau
  have hdualTau : CenterNeutral (asRepresentation dualTau) :=
    (representationEquiv_centerNeutral_iff
      (dualUnitaryRepEquiv tau)).mpr hcenter.dual
  let target := centerQuotientUnitaryRepData dualTau hdualTau
  obtain ⟨m, Tq, hTq⟩ := faithful_selfDual_tensorPower_mapsTo_rep
    source (conjSpanCenterQuotientUnitaryRepData_injective sigma hsigma)
      (conjSpanCenterQuotientSelfDual sigma hsigma) target
  let Tcoord : IntertwiningMap
      (tensorPower (asRepresentation (hilbertConjSpanUnitaryRepData sigma)) m)
      (asRepresentation dualTau) := {
    toLinearMap := Tq.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      have h := IntertwiningMap.isIntertwining
        (tensorPower (asRepresentation source) m)
        (asRepresentation target) Tq g x
      simpa [source, target, dualTau, tensorPower_apply,
        centerQuotientUnitaryRepData_coe] using h }
  let sourceEquiv := tensorPowerEquiv
    (hilbertConjSpanCoordinateEquiv sigma).symm m
  let targetEquiv := dualUnitaryRepEquiv tau
  let T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation tau).dual :=
    targetEquiv.toIntertwiningMap.comp
      (Tcoord.comp sourceEquiv.toIntertwiningMap)
  refine ⟨m, T, ?_⟩
  intro hT
  apply hTq
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := sourceEquiv.toLinearEquiv.surjective x
  have happ := congrArg
    (fun S : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation tau).dual => S y) hT
  apply targetEquiv.toLinearEquiv.injective
  simpa [T, Tcoord, sourceEquiv, targetEquiv] using happ

/-- For an irreducible positive-dimensional Wilson representation, center
neutrality is exactly the existence of the operational conjugation-span
screening map. -/
theorem centerNeutral_iff_exists_conjSpanIntertwiner
    (sigma : ContinuousUnitaryRepData G n)
    (hsigma : Function.Injective sigma.ρ)
    (tau : ContinuousUnitaryRepData G p)
    (htau : (asRepresentation tau).IsIrreducible) :
    CenterNeutral (asRepresentation tau) ↔
      ∃ m : ℕ, ∃ T : IntertwiningMap
        (tensorPower (conjSpanRep sigma) m) (asRepresentation tau).dual,
        T ≠ 0 := by
  constructor
  · exact centerNeutral_exists_conjSpanIntertwiner sigma hsigma tau
  · intro hscreen
    letI : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp tau.dimension_pos
    letI : (asRepresentation tau).IsIrreducible := htau
    letI : (asRepresentation tau).dual.IsIrreducible :=
      isIrreducible_dual (asRepresentation tau)
    obtain ⟨m, T, hT⟩ := hscreen
    apply centerNeutral_of_dual
    exact centerNeutral_of_nonzero_intertwiner_to_irreducible T hT
      ((conjSpanRep_kernelIsCenter sigma hsigma).centerNeutral.tensorPower m)

end

end YangMills.Gluelump.RepresentationTheory
