/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ArmPath
import GluelumpPerimeterLaw.Endpoint.ConjugationSpanField
import YangMills.Gauge.FiniteVolume

/-!
# Screened Wilson lines from the direct conjugation-span endpoint

This is the narrow adapter from `conjSpanPhi` to the generic screened
observable and reflection-positivity infrastructure.
-/

namespace YangMills.Gluelump.Endpoint

open MeasureTheory YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open YangMills.Gluelump.RepresentationTheory
open Representation

noncomputable section

variable {G : Type*} {d m n p : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-! ## Path observables -/

/-- The screened Wilson line with the normalized direct endpoint at each
end. -/
def conjSpanScreenedWilsonLine
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y) :
    LocalObservable d G :=
  screenedObservable rho (conjSpanPhi hd sigma rho T x)
    (conjSpanPhi hd sigma rho T y) gamma

@[simp]
theorem conjSpanScreenedWilsonLine_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    (Q : Configuration d G) :
    conjSpanScreenedWilsonLine hd sigma rho T gamma Q =
      hermitianPairing (conjSpanPhi hd sigma rho T x Q)
        (dualAction rho (holonomy Q gamma)
          (conjSpanPhi hd sigma rho T y Q)) :=
  rfl

@[simp]
theorem conjSpanScreenedWilsonLine_support
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y) :
    (conjSpanScreenedWilsonLine hd sigma rho T gamma).support =
      basedLoopSupport (combLoops (m := m) hd x) ∪
        basedLoopSupport (combLoops (m := m) hd y) ∪
          gamma.edgeSupport := by
  rfl

theorem conjSpanScreenedWilsonLine_gaugeInvariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y) :
    IsGaugeInvariant (conjSpanScreenedWilsonLine hd sigma rho T gamma) :=
  screenedObservable_gaugeInvariant rho _ _ gamma
    (conjSpanPhi_gauge_covariant hd sigma rho T x)
    (conjSpanPhi_gauge_covariant hd sigma rho T y)

theorem norm_conjSpanScreenedWilsonLine_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    (Q : Configuration d G) :
    ‖conjSpanScreenedWilsonLine hd sigma rho T gamma Q‖ ≤ 1 :=
  norm_screenedValue_le_one rho _ _ gamma Q
    (conjSpanPhi_l2Norm_le_one hd sigma rho T x Q)
    (conjSpanPhi_l2Norm_le_one hd sigma rho T y Q)

/-! ## Translation, reversal, and reflection -/

/-- Translate the path and both endpoint copies together. -/
def conjSpanScreenedWilsonLineTranslated
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (v : Site d) {x y : Site d} (gamma : Lattice.Cubic.Path x y) :
    LocalObservable d G :=
  screenedObservable rho
    (conjSpanPhiTranslated hd sigma rho T v x)
    (conjSpanPhiTranslated hd sigma rho T v y)
    (gamma.translate v)

/-- The translated observable is the original observable evaluated on the
translated configuration. -/
@[simp]
theorem conjSpanScreenedWilsonLineTranslated_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (v : Site d) {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    (Q : Configuration d G) :
    conjSpanScreenedWilsonLineTranslated hd sigma rho T v gamma Q =
      conjSpanScreenedWilsonLine hd sigma rho T gamma
        (LocalObservable.translateConfiguration v Q) := by
  rw [conjSpanScreenedWilsonLineTranslated, screenedObservable_apply,
    screenedValue_eq_hermitianPairing,
    conjSpanScreenedWilsonLine_apply,
    conjSpanPhiTranslated_apply, conjSpanPhiTranslated_apply]
  rw [← holonomy_translateConfiguration v Q gamma]
  rfl

/-- Reversing the path swaps endpoints and complex-conjugates the line. -/
theorem conjSpanScreenedWilsonLine_reverse_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    (Q : Configuration d G) :
    conjSpanScreenedWilsonLine hd sigma rho T gamma.reverse Q =
      star (conjSpanScreenedWilsonLine hd sigma rho T gamma Q) := by
  exact screenedObservable_reverse_apply rho
    (conjSpanPhi hd sigma rho T x) (conjSpanPhi hd sigma rho T y) gamma Q

/-- Exact link-reflection identity consumed by crossing-link reflection
positivity. -/
theorem linkTheta_conjSpanScreenedWilsonLine_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    (axis : Fin d) (cut : ℤ) (Q : Configuration d G) :
    (conjSpanScreenedWilsonLine hd sigma rho T gamma).linkTheta axis cut Q =
      screenedObservable rho
        (conjSpanPhiLinkReflected hd sigma rho T y axis cut)
        (conjSpanPhiLinkReflected hd sigma rho T x axis cut)
        ((gamma.linkReflect axis cut).reverse) Q := by
  exact linkTheta_screenedObservable_apply rho
    (conjSpanPhi hd sigma rho T x) (conjSpanPhi hd sigma rho T y)
    gamma axis cut Q

/-- Exact diagonal-reflection identity, with the path and endpoint copies
reflected by the same affine involution. -/
theorem diagonalTheta_conjSpanScreenedWilsonLine_apply
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    {x y : Site d} (gamma : Lattice.Cubic.Path x y)
    {axis₁ axis₂ : Fin d} (haxes : axis₁ ≠ axis₂)
    (cut : ℤ) (Q : Configuration d G) :
    (conjSpanScreenedWilsonLine hd sigma rho T gamma).diagonalTheta
        axis₁ axis₂ cut Q =
      screenedObservable rho
        (conjSpanPhiDiagonalReflected hd sigma rho T y axis₁ axis₂ cut)
        (conjSpanPhiDiagonalReflected hd sigma rho T x axis₁ axis₂ cut)
        ((gamma.diagonalReflect axis₁ axis₂ haxes cut).reverse) Q := by
  exact diagonalTheta_screenedObservable_apply rho
    (conjSpanPhi hd sigma rho T x) (conjSpanPhi hd sigma rho T y)
    gamma haxes cut Q

/-! ## Distinguished one-link observable -/

/-- Direct screened observable on the distinguished unit arm bond. -/
def conjSpanScreenedOneLink
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) : LocalObservable d G :=
  conjSpanScreenedWilsonLine hd sigma rho T (armBondPath hd x)

theorem conjSpanScreenedOneLink_gaugeInvariant
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) :
    IsGaugeInvariant (conjSpanScreenedOneLink hd sigma rho T x) :=
  conjSpanScreenedWilsonLine_gaugeInvariant hd sigma rho T
    (armBondPath hd x)

theorem norm_conjSpanScreenedOneLink_le_one
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (Q : Configuration d G) :
    ‖conjSpanScreenedOneLink hd sigma rho T x Q‖ ≤ 1 :=
  norm_conjSpanScreenedWilsonLine_le_one hd sigma rho T
    (armBondPath hd x) Q

def conjSpanScreenedOneLinkCorrelation
    [MeasurableSpace G]
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (mu : Measure (Configuration d G)) : ℂ :=
  ∫ Q, conjSpanScreenedOneLink hd sigma rho T x Q ∂mu

def finiteConjSpanScreenedOneLinkCorrelation
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [GaugeHaarProbability G]
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G p)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (x : Site d) (Lambda : FiniteSpecification d G)
    (potential : RealPlaquettePotential G) (beta : ℝ) : ℂ :=
  ∫ U, conjSpanScreenedOneLink hd sigma rho T x (Lambda.evaluate U)
    ∂FiniteVolume.gibbsMeasure Lambda potential beta

end

end YangMills.Gluelump.Endpoint
