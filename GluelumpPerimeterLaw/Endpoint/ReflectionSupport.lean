/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.AntiDiagonalReflection
import GluelumpPerimeterLaw.Endpoint.Observable

/-!
# Reflection support certificates for gluelump endpoints

The existing reflection-positive algebras are stated for scalar local
observables.  This file gives endpoint fields and transport paths the same
three support predicates and proves that a screened contraction belongs to a
positive algebra whenever both collars and the joining path do.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson

noncomputable section

namespace EdgeSet

/-- Every edge lies on or above the coordinate site plane `x τ = k`. -/
def SupportedInSitePositiveHalf {d : ℕ} (τ : Fin d) (k : ℤ)
    (S : Finset (PositiveEdge d)) : Prop :=
  ∀ e ∈ S, k ≤ e.source τ

/-- Every edge lies in the link-positive half-lattice; perpendicular edges
crossing `x τ = k + 1/2` are allowed. -/
def SupportedInLinkPositiveHalf {d : ℕ} (τ : Fin d) (k : ℤ)
    (S : Finset (PositiveEdge d)) : Prop :=
  ∀ e ∈ S, k < e.target τ

/-- Every edge, including both endpoints, lies in the positive half-lattice
of the affine diagonal plane `x τ - x σ = k`. -/
def SupportedInDiagonalPositiveHalf {d : ℕ} (τ σ : Fin d) (k : ℤ)
    (S : Finset (PositiveEdge d)) : Prop :=
  ∀ e ∈ S,
    k ≤ e.source τ - e.source σ ∧ k ≤ e.target τ - e.target σ

/-- Every edge, including both endpoints, lies in the positive half-lattice
of the affine anti-diagonal plane `x τ + x σ = k`. -/
def SupportedInAntiDiagonalPositiveHalf {d : ℕ} (τ σ : Fin d) (k : ℤ)
    (S : Finset (PositiveEdge d)) : Prop :=
  ∀ e ∈ S,
    k ≤ e.source τ + e.source σ ∧ k ≤ e.target τ + e.target σ

theorem site_union {d : ℕ} {τ : Fin d} {k : ℤ}
    {S T : Finset (PositiveEdge d)}
    (hS : SupportedInSitePositiveHalf τ k S)
    (hT : SupportedInSitePositiveHalf τ k T) :
    SupportedInSitePositiveHalf τ k (S ∪ T) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hS e he
  · exact hT e he

theorem link_union {d : ℕ} {τ : Fin d} {k : ℤ}
    {S T : Finset (PositiveEdge d)}
    (hS : SupportedInLinkPositiveHalf τ k S)
    (hT : SupportedInLinkPositiveHalf τ k T) :
    SupportedInLinkPositiveHalf τ k (S ∪ T) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hS e he
  · exact hT e he

theorem diagonal_union {d : ℕ} {τ σ : Fin d} {k : ℤ}
    {S T : Finset (PositiveEdge d)}
    (hS : SupportedInDiagonalPositiveHalf τ σ k S)
    (hT : SupportedInDiagonalPositiveHalf τ σ k T) :
    SupportedInDiagonalPositiveHalf τ σ k (S ∪ T) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hS e he
  · exact hT e he

theorem antiDiagonal_union {d : ℕ} {τ σ : Fin d} {k : ℤ}
    {S T : Finset (PositiveEdge d)}
    (hS : SupportedInAntiDiagonalPositiveHalf τ σ k S)
    (hT : SupportedInAntiDiagonalPositiveHalf τ σ k T) :
    SupportedInAntiDiagonalPositiveHalf τ σ k (S ∪ T) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hS e he
  · exact hT e he

end EdgeSet

namespace LocalField

variable {d n : ℕ} {G : Type*} [TopologicalSpace G]

def SupportedInSitePositiveHalf (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : Prop :=
  EdgeSet.SupportedInSitePositiveHalf τ k Phi.support

def SupportedInLinkPositiveHalf (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : Prop :=
  EdgeSet.SupportedInLinkPositiveHalf τ k Phi.support

def SupportedInDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : Prop :=
  EdgeSet.SupportedInDiagonalPositiveHalf τ σ k Phi.support

def SupportedInAntiDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : Prop :=
  EdgeSet.SupportedInAntiDiagonalPositiveHalf τ σ k Phi.support

/-- Moving a link-positive cutting plane toward the negative side preserves
positive-half support. -/
theorem SupportedInLinkPositiveHalf.mono {τ : Fin d} {k l : ℤ}
    {Phi : LocalField d G (Fin n → ℂ)}
    (hPhi : Phi.SupportedInLinkPositiveHalf τ l) (hkl : k ≤ l) :
    Phi.SupportedInLinkPositiveHalf τ k := by
  intro e he
  exact lt_of_le_of_lt hkl (hPhi e he)

end LocalField

namespace Path

variable {d : ℕ} {x y : Site d}

def SupportedInSitePositiveHalf (τ : Fin d) (k : ℤ)
    (gamma : Lattice.Cubic.Path x y) : Prop :=
  EdgeSet.SupportedInSitePositiveHalf τ k gamma.edgeSupport

def SupportedInLinkPositiveHalf (τ : Fin d) (k : ℤ)
    (gamma : Lattice.Cubic.Path x y) : Prop :=
  EdgeSet.SupportedInLinkPositiveHalf τ k gamma.edgeSupport

def SupportedInDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (gamma : Lattice.Cubic.Path x y) : Prop :=
  EdgeSet.SupportedInDiagonalPositiveHalf τ σ k gamma.edgeSupport

def SupportedInAntiDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (gamma : Lattice.Cubic.Path x y) : Prop :=
  EdgeSet.SupportedInAntiDiagonalPositiveHalf τ σ k gamma.edgeSupport

/-- Moving a link-positive cutting plane toward the negative side preserves
positive-half path support. -/
theorem SupportedInLinkPositiveHalf.mono {τ : Fin d} {k l : ℤ}
    {gamma : Lattice.Cubic.Path x y}
    (hgamma : SupportedInLinkPositiveHalf τ l gamma) (hkl : k ≤ l) :
    SupportedInLinkPositiveHalf τ k gamma := by
  intro e he
  exact lt_of_le_of_lt hkl (hgamma e he)

end Path

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The scalar screened contraction inherits coordinate-site support from its
two endpoint collars and joining path. -/
theorem screenedObservable_supportedInSitePositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (τ : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInSitePositiveHalf τ k)
    (hPsi : Psi.SupportedInSitePositiveHalf τ k)
    (hgamma : Path.SupportedInSitePositiveHalf τ k gamma) :
    (screenedObservable rho Phi Psi gamma).SupportedInSitePositiveHalf τ k := by
  change EdgeSet.SupportedInSitePositiveHalf τ k
    (screenedObservable rho Phi Psi gamma).support
  rw [screenedObservable_support]
  exact EdgeSet.site_union (EdgeSet.site_union hPhi hPsi) hgamma

/-- The scalar screened contraction inherits link-positive support, including
the allowed crossing perpendicular link. -/
theorem screenedObservable_supportedInLinkPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (τ : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInLinkPositiveHalf τ k)
    (hPsi : Psi.SupportedInLinkPositiveHalf τ k)
    (hgamma : Path.SupportedInLinkPositiveHalf τ k gamma) :
    (screenedObservable rho Phi Psi gamma).SupportedInLinkPositiveHalf τ k := by
  change EdgeSet.SupportedInLinkPositiveHalf τ k
    (screenedObservable rho Phi Psi gamma).support
  rw [screenedObservable_support]
  exact EdgeSet.link_union (EdgeSet.link_union hPhi hPsi) hgamma

/-- The scalar screened contraction inherits diagonal-positive support from
both collars and the joining path. -/
theorem screenedObservable_supportedInDiagonalPositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (τ σ : Fin d) (k : ℤ)
    (hPhi : Phi.SupportedInDiagonalPositiveHalf τ σ k)
    (hPsi : Psi.SupportedInDiagonalPositiveHalf τ σ k)
    (hgamma : Path.SupportedInDiagonalPositiveHalf τ σ k gamma) :
    (screenedObservable rho Phi Psi gamma).SupportedInDiagonalPositiveHalf
      τ σ k := by
  change EdgeSet.SupportedInDiagonalPositiveHalf τ σ k
    (screenedObservable rho Phi Psi gamma).support
  rw [screenedObservable_support]
  exact EdgeSet.diagonal_union (EdgeSet.diagonal_union hPhi hPsi) hgamma

end

end YangMills.Gluelump.Endpoint
