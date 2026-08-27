/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Reflection

/-!
# Measure-independent row-vector diagonal bending

This file contains the pointwise path, family-product, and support identities
used by the first corner reflection.  It deliberately contains no choice of
Gibbs state or thermodynamic-limit construction.
-/

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Reflect a path ending on the diagonal plane and cast its reflected target
back to the same fixed vertex. -/
def diagonalReflectedPathToFixed
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z) :
    Lattice.Cubic.Path (diagonalReflection tau sigma k x) z :=
  YangMills.Basic.OrientedPath.castTarget
    (p.diagonalReflect tau sigma hts k) hz

@[simp]
theorem holonomy_diagonalReflectedPathToFixed
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z)
    (A : Configuration d G) :
    holonomy A (diagonalReflectedPathToFixed hts k p hz) =
      holonomy (diagonalReflectConfiguration tau sigma k A) p := by
  unfold diagonalReflectedPathToFixed
  rw [holonomy_castTarget,
    holonomy_diagonalReflectConfiguration_path hts]

/-- The trace pairing of the transported endpoint row with an endpoint at the
fixed vertex is exactly the corresponding reflected screened line. -/
theorem diagonalIncoming_endpoint_familyProduct_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Xi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z)
    (A : Configuration d G) :
    (∑ i, (incomingHalfComponent rho Phi p i).diagonalReflectionProduct
        tau sigma k (Xi.component i) A) =
      screenedObservable rho (Phi.diagonalPullback tau sigma k) Xi
        (diagonalReflectedPathToFixed hts k p hz) A := by
  rw [screenedObservable_apply]
  unfold screenedValue
  have hpair := representationAction_pairing rho
    (holonomy A (diagonalReflectedPathToFixed hts k p hz))
    (representationAction rho
      (holonomy A (diagonalReflectedPathToFixed hts k p hz))⁻¹
      (Phi.diagonalPullback tau sigma k A)) (Xi A)
  have hcancel :
      representationAction rho (holonomy A (diagonalReflectedPathToFixed hts k p hz))
        (representationAction rho
          (holonomy A (diagonalReflectedPathToFixed hts k p hz))⁻¹
          (Phi.diagonalPullback tau sigma k A)) =
        Phi.diagonalPullback tau sigma k A := by
    rw [← representationAction_mul]
    simp
  rw [hcancel] at hpair
  simp only [LocalObservable.diagonalReflectionProduct_apply,
    incomingHalfComponent_apply, LocalField.component_apply,
    LocalField.diagonalPullback_apply,
    holonomy_diagonalReflectedPathToFixed]
  simpa only [LocalField.diagonalPullback_apply,
    holonomy_diagonalReflectedPathToFixed] using hpair.symm

/-- The row's diagonal self-pairing is the L-shaped screened observable whose
path runs along the reflected arm and returns along the original arm. -/
theorem diagonalIncoming_familySelfProduct_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z)
    (A : Configuration d G) :
    (∑ i, (incomingHalfComponent rho Phi p i).diagonalReflectionProduct
        tau sigma k (incomingHalfComponent rho Phi p i) A) =
      screenedObservable rho (Phi.diagonalPullback tau sigma k) Phi
        ((diagonalReflectedPathToFixed hts k p hz).comp p.reverse) A := by
  rw [screenedObservable_apply, screenedValue_comp_eq_halfGram]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [LocalObservable.diagonalReflectionProduct_apply,
    incomingHalfComponent_apply, outgoingHalfComponent_apply,
    LocalField.diagonalPullback_apply,
    holonomy_diagonalReflectedPathToFixed, holonomy_reverse]

/-- Support of every transported row coordinate follows directly from the
endpoint collar and the arm support. -/
theorem incomingHalfComponent_supportedInDiagonalPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    {x z : Site d} (p : Lattice.Cubic.Path x z) (i : Fin n)
    (tau sigma : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInDiagonalPositiveHalf tau sigma k)
    (hp : Endpoint.Path.SupportedInDiagonalPositiveHalf tau sigma k p) :
    (incomingHalfComponent rho Phi p i).SupportedInDiagonalPositiveHalf
      tau sigma k := by
  intro e he
  change e ∈ Phi.support ∪ p.edgeSupport at he
  rcases Finset.mem_union.mp he with he | he
  · exact hPhi e he
  · exact hp e he

end

end YangMills.Gluelump.Propagation
