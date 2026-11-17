/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.GaugeFixedFactorization

/-!
# Exact split of finite side coordinates

For a fixed finite collar predicate on a finite side-coordinate type, product
Haar splits exactly into the collar coordinates and their complement.  These
declarations are the measure-preserving reindexing layer needed by the
concrete gauge-fixed one-link adapter; no normalization factor is introduced.
-/

namespace YangMills.Gluelump.OneLink

open MeasureTheory Gauge

noncomputable section

variable {G P : Type*} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [BorelSpace G] [GaugeHaarProbability G]
  [Fintype P]

/-- Side coordinates selected for the fixed endpoint collar. -/
abbrev CollarCoordinate (selected : P → Prop) := Subtype selected

/-- All side coordinates outside the fixed endpoint collar. -/
abbrev RemoteCoordinate (selected : P → Prop) :=
  {p : P // ¬ selected p}

/-- The canonical split of a side configuration into collar and remote
coordinates. -/
def splitSideMeasurableEquiv (selected : P → Prop)
    [DecidablePred selected] :
    (P → G) ≃ᵐ ((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : P ↦ G) selected

@[simp]
theorem splitSideMeasurableEquiv_apply_fst
    (selected : P → Prop) [DecidablePred selected]
    (U : P → G) (p : CollarCoordinate selected) :
    (splitSideMeasurableEquiv (G := G) selected U).1 p = U p.1 :=
  rfl

@[simp]
theorem splitSideMeasurableEquiv_apply_snd
    (selected : P → Prop) [DecidablePred selected]
    (U : P → G) (p : RemoteCoordinate selected) :
    (splitSideMeasurableEquiv (G := G) selected U).2 p = U p.1 :=
  rfl

/-- Splitting coordinates is continuous for product topologies. -/
theorem continuous_splitSide
    (selected : P → Prop) [DecidablePred selected] :
    Continuous (splitSideMeasurableEquiv (G := G) selected) := by
  simpa only [splitSideMeasurableEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd] using
    (Homeomorph.piEquivPiSubtypeProd selected (fun _ : P ↦ G)).continuous

/-- Merging collar and remote coordinates is continuous. -/
theorem continuous_mergeSide
    (selected : P → Prop) [DecidablePred selected] :
    Continuous (splitSideMeasurableEquiv (G := G) selected).symm := by
  simpa only [splitSideMeasurableEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd] using
    (Homeomorph.piEquivPiSubtypeProd selected (fun _ : P ↦ G)).symm.continuous

/-- Merging two split configurations with the same remote component gives
the same value at every unselected coordinate. -/
theorem mergeSide_apply_of_not_selected
    (selected : P → Prop) [DecidablePred selected]
    (u u' : CollarCoordinate selected → G)
    (r : RemoteCoordinate selected → G) (p : P) (hp : ¬selected p) :
    (splitSideMeasurableEquiv (G := G) selected).symm (u, r) p =
      (splitSideMeasurableEquiv (G := G) selected).symm (u', r) p := by
  simp [splitSideMeasurableEquiv, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, hp]

/-- Exact product-Haar preservation of the collar/remote split. -/
theorem measurePreserving_splitSide
    (selected : P → Prop) [DecidablePred selected] :
    MeasurePreserving (splitSideMeasurableEquiv (G := G) selected)
      (ProductHaar.measure G P)
      ((ProductHaar.measure G (CollarCoordinate selected)).prod
        (ProductHaar.measure G (RemoteCoordinate selected))) := by
  simpa only [ProductHaar.measure] using
    (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun _ : P ↦ GaugeHaarProbability.haar G) selected)

/-- Product Haar introduces no constant when a side integral is written in
collar/remote coordinates. -/
theorem integral_comp_splitSide
    (selected : P → Prop) [DecidablePred selected]
    (f : ((CollarCoordinate selected → G) ×
      (RemoteCoordinate selected → G)) → ℂ) :
    ∫ U, f (splitSideMeasurableEquiv (G := G) selected U)
        ∂ProductHaar.measure G P =
      ∫ z, f z ∂((ProductHaar.measure G (CollarCoordinate selected)).prod
        (ProductHaar.measure G (RemoteCoordinate selected))) := by
  exact (measurePreserving_splitSide (G := G) selected).integral_comp' f

/-- A finset included in a larger finset is canonically equivalent to the
selected-coordinate subtype of the larger finset. -/
def finsetEquivCollarCoordinate
    {R : Type*} [DecidableEq R] (S Pset : Finset R) (hSP : S ⊆ Pset) :
    S ≃ CollarCoordinate (P := Pset) (fun p ↦ p.1 ∈ S) where
  toFun s := ⟨⟨s.1, hSP s.2⟩, s.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv s := Subtype.ext rfl
  right_inv p := Subtype.ext (Subtype.ext rfl)

end

end YangMills.Gluelump.OneLink
