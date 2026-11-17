/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ReflectionSupport

/-!
# Reflected endpoint fields and screened observables

Vector-valued endpoint fields pull back along the concrete link and diagonal
configuration reflections.  Hermitian symmetry, unitarity of the ordinary
representation action, and path-holonomy covariance then identify the reflected screened
observable with the same construction having its endpoints exchanged and
its reflected path reversed.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Reversing the transport path and exchanging its endpoint fields complex
conjugates the screened scalar. -/
theorem screenedObservable_reverse_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (A : Configuration d G) :
    screenedObservable rho Psi Phi gamma.reverse A =
      star (screenedObservable rho Phi Psi gamma A) := by
  rw [screenedObservable_apply, screenedObservable_apply,
    screenedValue_eq_hermitianPairing,
    screenedValue_eq_hermitianPairing, holonomy_reverse]
  exact (star_hermitianPairing_representationAction rho (holonomy A gamma)
    (Phi A) (Psi A)).symm

/-- Pull an endpoint field back through an integer coordinate reflection.
This is the vector-valued analogue of
`LocalObservable.siteReflectionPullback`; it is useful for putting a corner
endpoint collar entirely into one diagonal half-lattice. -/
def LocalField.sitePullback (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : LocalField d G (Fin n → ℂ) where
  toContinuousMap := Phi.toContinuousMap.comp
    ⟨siteReflectConfiguration τ k,
      continuous_siteReflectConfiguration τ k⟩
  support := Phi.support.image (PositiveEdge.siteReflect τ k)
  dependsOn_support := by
    intro A B hAB
    apply Phi.dependsOn_support
    intro e he
    have href := hAB (e.siteReflect τ k)
      (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    change (if e.direction = τ then
        (A (e.siteReflect τ k))⁻¹ else A (e.siteReflect τ k)) =
      (if e.direction = τ then
        (B (e.siteReflect τ k))⁻¹ else B (e.siteReflect τ k))
    by_cases hd : e.direction = τ
    · simp only [hd, if_true, href]
    · simp only [hd, if_false, href]

@[simp]
theorem LocalField.sitePullback_apply (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) (A : Configuration d G) :
    Phi.sitePullback τ k A = Phi (siteReflectConfiguration τ k A) :=
  rfl

/-- Coordinate reflection does not change the pointwise normalization of a
local endpoint field. -/
theorem LocalField.sitePullback_l2Norm_le_one
    (Phi : LocalField d G (Fin n → ℂ)) (τ : Fin d) (k : ℤ)
    (hPhi : ∀ A, endpointL2Norm (Phi A) ≤ 1) (A : Configuration d G) :
    endpointL2Norm (Phi.sitePullback τ k A) ≤ 1 := by
  rw [LocalField.sitePullback_apply]
  exact hPhi _

/-- Pull an endpoint field back through a half-integer link reflection. -/
def LocalField.linkPullback (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : LocalField d G (Fin n → ℂ) where
  toContinuousMap := Phi.toContinuousMap.comp
    ⟨linkReflectConfiguration τ k,
      continuous_linkReflectConfiguration τ k⟩
  support := Phi.support.image (PositiveEdge.linkReflect τ k)
  dependsOn_support := by
    intro A B hAB
    apply Phi.dependsOn_support
    intro e he
    have href : e.linkReflect τ k ∈
        Phi.support.image (PositiveEdge.linkReflect τ k) :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    change linkReflectConfiguration τ k A e =
      linkReflectConfiguration τ k B e
    unfold linkReflectConfiguration
    by_cases hd : e.direction = τ
    · simp only [hd, if_true, hAB (e.linkReflect τ k) href]
    · simp only [hd, if_false, hAB (e.linkReflect τ k) href]

@[simp]
theorem LocalField.linkPullback_apply (τ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) (A : Configuration d G) :
    Phi.linkPullback τ k A = Phi (linkReflectConfiguration τ k A) :=
  rfl

/-- Pulling back a covariant endpoint through link reflection moves its base
site through the same reflection. -/
theorem GaugeCovariantAt.linkPullback
    (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : GaugeCovariantAt rho x Phi) (τ : Fin d) (k : ℤ) :
    GaugeCovariantAt rho (linkReflection τ k x)
      (Phi.linkPullback τ k) := by
  intro g A
  rw [LocalField.linkPullback_apply, LocalField.linkPullback_apply,
    linkReflectConfiguration_gaugeTransform, hPhi]

/-- Pull an endpoint field back through an affine diagonal reflection. -/
def LocalField.diagonalPullback (τ σ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) : LocalField d G (Fin n → ℂ) where
  toContinuousMap := Phi.toContinuousMap.comp
    ⟨diagonalReflectConfiguration τ σ k,
      continuous_diagonalReflectConfiguration τ σ k⟩
  support := Phi.support.image (PositiveEdge.diagonalReflect τ σ k)
  dependsOn_support := by
    intro A B hAB
    apply Phi.dependsOn_support
    intro e he
    exact hAB (e.diagonalReflect τ σ k)
      (Finset.mem_image.mpr ⟨e, he, rfl⟩)

@[simp]
theorem LocalField.diagonalPullback_apply (τ σ : Fin d) (k : ℤ)
    (Phi : LocalField d G (Fin n → ℂ)) (A : Configuration d G) :
    Phi.diagonalPullback τ σ k A =
      Phi (diagonalReflectConfiguration τ σ k A) :=
  rfl

/-- Pulling back a covariant endpoint through diagonal reflection moves its
base site through the same affine reflection. -/
theorem GaugeCovariantAt.diagonalPullback
    (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : GaugeCovariantAt rho x Phi)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    GaugeCovariantAt rho (diagonalReflection τ σ k x)
      (Phi.diagonalPullback τ σ k) := by
  intro g A
  rw [LocalField.diagonalPullback_apply, LocalField.diagonalPullback_apply,
    diagonalReflectConfiguration_gaugeTransform hτσ, hPhi]

/-- Link reflection exchanges the two screened endpoints and reverses the
reflected transport path. -/
theorem linkTheta_screenedObservable_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) (τ : Fin d) (k : ℤ)
    (A : Configuration d G) :
    (screenedObservable rho Phi Psi gamma).linkTheta τ k A =
      screenedObservable rho (Psi.linkPullback τ k) (Phi.linkPullback τ k)
        ((gamma.linkReflect τ k).reverse) A := by
  rw [LocalObservable.linkTheta_apply,
    screenedObservable_apply, screenedObservable_apply,
    screenedValue_eq_hermitianPairing,
    screenedValue_eq_hermitianPairing,
    LocalField.linkPullback_apply, LocalField.linkPullback_apply,
    holonomy_reverse, ← holonomy_linkReflectConfiguration]
  exact star_hermitianPairing_representationAction rho
    (holonomy (linkReflectConfiguration τ k A) gamma) _ _

/-- Diagonal reflection exchanges the two screened endpoints and reverses the
reflected transport path. -/
theorem diagonalTheta_screenedObservable_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ)) {x y : Site d}
    (gamma : Lattice.Cubic.Path x y) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (A : Configuration d G) :
    (screenedObservable rho Phi Psi gamma).diagonalTheta τ σ k A =
      screenedObservable rho (Psi.diagonalPullback τ σ k)
        (Phi.diagonalPullback τ σ k)
        ((gamma.diagonalReflect τ σ hτσ k).reverse) A := by
  rw [LocalObservable.diagonalTheta_apply,
    screenedObservable_apply, screenedObservable_apply,
    screenedValue_eq_hermitianPairing,
    screenedValue_eq_hermitianPairing,
    LocalField.diagonalPullback_apply, LocalField.diagonalPullback_apply,
    holonomy_reverse, ← holonomy_diagonalReflectConfiguration_path hτσ]
  exact star_hermitianPairing_representationAction rho
    (holonomy (diagonalReflectConfiguration τ σ k A) gamma) _ _

end

end YangMills.Gluelump.Endpoint
