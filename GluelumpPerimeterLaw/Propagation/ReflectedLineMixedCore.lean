/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.ReflectedLineCore

/-!
# Mixed reflected screened lines

The scalar reflected-line norm square is not by itself enough for adjacent
length propagation.  The representation coordinate must remain visible while
two different positive half-arms are paired.  This file constructs that mixed
finite Gram family and packages it together with its two self-pairings.
-/

namespace YangMills.Gluelump.Propagation

open Filter Gauge Lattice.Cubic Wilson
open Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Join the reflected reverse of one positive half-arm to a possibly
different positive half-arm through the same distinguished crossing link. -/
def reflectedMixedFullPath (τ : Fin d) (k : ℤ) (z : Site d)
    (hz : z τ = k) {y u : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (r : Lattice.Cubic.Path (step z (.forward τ)) u) :
    Lattice.Cubic.Path (linkReflection τ k y) u :=
  (reflectedIncomingPath τ k z hz q).comp (crossingThenPath τ z r)

/-- The mixed reflected screened observable associated to two positive
endpoint/half-arm pairs. -/
def reflectedMixedObservable
    (rho : ContinuousUnitaryRepData G n)
    (Psi Xi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (r : Lattice.Cubic.Path (step z (.forward τ)) u) :
    LocalObservable d G :=
  screenedObservable rho (Psi.linkPullback τ k) Xi
    (reflectedMixedFullPath τ k z hz q r)

/-- On the fixed crossing slice, two different reflected half-arms give the
mixed pairing of the same finite Gram-coordinate families used by their two
self-reflected lines. -/
theorem reflectedMixedFullPath_isGaugeFixedLinkFamilyPairing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (rho : ContinuousUnitaryRepData G n)
    (Psi Xi : LocalField d G (Fin n → ℂ))
    (z : Site d) (hz : z τ = k) {y u : Site d}
    (q : Lattice.Cubic.Path (step z (.forward τ)) y)
    (r : Lattice.Cubic.Path (step z (.forward τ)) u)
    (hPsi : GaugeCovariantAt rho y Psi)
    (hXi : GaugeCovariantAt rho u Xi)
    (hdyn : (reflectedMixedObservable rho Psi Xi τ k z hz q r).support ⊆
      Λ.dynamicEdges)
    (hecross : crossingPositiveEdge z τ ∈ Λ.linkCrossingEdges τ k)
    (hinq : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i).conj.linkTheta τ k))
    (hinr : ∀ i, LocalObservable.SupportedInLinkPositiveHalf τ k
      ((incomingHalfComponent rho (Xi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz r) i).conj.linkTheta τ k))
    (houtr : ∀ i, (outgoingHalfComponent rho Xi
      (crossingThenPath τ z r) i).SupportedInLinkPositiveHalf τ k) :
    Λ.IsGaugeFixedLinkFamilyPairing τ k hΛ
      (reflectedMixedObservable rho Psi Xi τ k z hz q r)
      (fun i => linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho (Psi.linkPullback τ k)
          (reflectedIncomingPath τ k z hz q) i))
      (fun i => linkRestrictNegativeObservable Λ τ k hΛ
        (incomingHalfComponent rho (Xi.linkPullback τ k)
          (reflectedIncomingPath τ k z hz r) i)) := by
  apply Λ.isGaugeFixedLinkFamilyPairing_of_gaugeInvariant τ k hΛ
    (reflectedMixedObservable rho Psi Xi τ k z hz q r)
    (fun i => linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho (Psi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz q) i))
    (fun i => linkRestrictNegativeObservable Λ τ k hΛ
      (incomingHalfComponent rho (Xi.linkPullback τ k)
        (reflectedIncomingPath τ k z hz r) i))
    (screenedObservable_gaugeInvariant rho (Psi.linkPullback τ k) Xi
      (reflectedMixedFullPath τ k z hz q r)
      (GaugeCovariantAt.linkPullback rho y Psi hPsi τ k) hXi)
    hdyn
  intro Uminus Uplus
  let A := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (Uminus, Uplus)))
  let B := Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, Uplus)))
  change screenedValue rho (Psi.linkPullback τ k) Xi
      ((reflectedIncomingPath τ k z hz q).comp
        (crossingThenPath τ z r)) A = _
  rw [screenedValue_comp_eq_halfGram]
  apply Finset.sum_congr rfl
  intro i _hi
  have hleft := linkRestrictNegativeObservable_apply_assemble_fixed
    Λ τ k hΛ
    (incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i) (hinq i) Uminus Uplus
  have houtA := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (outgoingHalfComponent rho Xi (crossingThenPath τ z r) i) (houtr i)
    (1, (Uminus, Uplus))
  have houtB := Λ.linkRestrictObservable_apply_assemble τ k hΛ
    (outgoingHalfComponent rho Xi (crossingThenPath τ z r) i) (houtr i)
    (1, (1, Uplus))
  have hcrossB : B (crossingPositiveEdge z τ) = 1 := by
    exact Λ.linkCrossingEdge_value_fixed τ k hΛ (1, Uplus)
      (crossingPositiveEdge z τ) hecross
  have hdrop := outgoingHalfComponent_crossingThenPath_eq_of_crossing_one
    rho Xi τ z r i B hcrossB
  have hmatch := linkRestrictNegative_reflectedIncoming_eq_outgoing_on_side
    Λ τ k hΛ rho Xi z hz r i (hinr i) Uplus
  change star (incomingHalfComponent rho (Psi.linkPullback τ k)
      (reflectedIncomingPath τ k z hz q) i A) *
      outgoingHalfComponent rho Xi (crossingThenPath τ z r) i A = _
  rw [hleft]
  have houtAB : outgoingHalfComponent rho Xi
      (crossingThenPath τ z r) i A =
      outgoingHalfComponent rho Xi (crossingThenPath τ z r) i B := by
    rw [houtA, houtB]
  rw [houtAB, hdrop, ← hmatch]

end

end YangMills.Gluelump.Propagation
