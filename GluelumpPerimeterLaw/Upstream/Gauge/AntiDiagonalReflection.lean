/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.DiagonalReflection
import GluelumpPerimeterLaw.Upstream.Gauge.InfiniteReflection
import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflection

/-!
# Anti-diagonal reflection by conjugating a diagonal reflection

Reflection through `x τ + x σ = k` is obtained for free by conjugating the
diagonal reflection through `x τ - x σ = k` with the coordinate flip
`x σ ↦ -x σ`.  This file records that conjugation at the site,
configuration, observable, and support levels.
-/

namespace YangMills.Lattice.Cubic

/-- Reflection through the affine anti-diagonal plane `x τ + x σ = k`. -/
def antiDiagonalReflection {d : ℕ} (τ σ : Fin d) (k : ℤ) (x : Site d) :
    Site d :=
  siteReflection σ 0 (diagonalReflection τ σ k (siteReflection σ 0 x))

@[simp]
theorem antiDiagonalReflection_apply_first {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    antiDiagonalReflection τ σ k x τ = k - x σ := by
  simp [antiDiagonalReflection, siteReflection_apply_ne hτσ]
  ring

@[simp]
theorem antiDiagonalReflection_apply_second {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    antiDiagonalReflection τ σ k x σ = k - x τ := by
  simp [antiDiagonalReflection, hτσ]

/-- A coordinate flip converts anti-diagonal height into diagonal height. -/
theorem siteReflection_diagonalDifference_eq_sum {d : ℕ}
    {τ σ : Fin d} (hτσ : τ ≠ σ) (x : Site d) :
    siteReflection σ 0 x τ - siteReflection σ 0 x σ = x τ + x σ := by
  simp [siteReflection_apply_ne hτσ]

namespace Path

/-- Reflect a typed path through `x τ + x σ = k`, using the same
coordinate-flip conjugation as for configurations. -/
def antiDiagonalReflect {d : ℕ} {x y : Site d} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Path x y) :
    Path (antiDiagonalReflection τ σ k x)
      (antiDiagonalReflection τ σ k y) :=
  ((p.siteReflect σ 0).diagonalReflect τ σ hτσ k).siteReflect σ 0

end Path

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Configuration reflection through `x τ + x σ = k`, defined by the
conjugation `Sσ ∘ Dτσk ∘ Sσ`. -/
def antiDiagonalReflectConfiguration (τ σ : Fin d) (k : ℤ)
    (A : Configuration d G) : Configuration d G :=
  siteReflectConfiguration σ 0
    (diagonalReflectConfiguration τ σ k
      (siteReflectConfiguration σ 0 A))

theorem continuous_antiDiagonalReflectConfiguration (τ σ : Fin d) (k : ℤ) :
    Continuous (antiDiagonalReflectConfiguration (G := G) τ σ k) := by
  exact (continuous_siteReflectConfiguration σ 0).comp
    ((continuous_diagonalReflectConfiguration τ σ k).comp
      (continuous_siteReflectConfiguration σ 0))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Holonomy covariance for anti-diagonal reflection. -/
@[simp]
theorem holonomy_antiDiagonalReflectConfiguration_path
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (A : Configuration d G) {x y : Site d}
    (p : Lattice.Cubic.Path x y) :
    holonomy (antiDiagonalReflectConfiguration τ σ k A) p =
      holonomy A (p.antiDiagonalReflect hτσ k) := by
  unfold antiDiagonalReflectConfiguration Path.antiDiagonalReflect
  rw [holonomy_siteReflectConfiguration,
    holonomy_diagonalReflectConfiguration_path hτσ,
    holonomy_siteReflectConfiguration]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem antiDiagonalReflectConfiguration_siteReflectConfiguration
    (τ σ : Fin d) (k : ℤ) (A : Configuration d G) :
    antiDiagonalReflectConfiguration τ σ k
        (siteReflectConfiguration σ 0 A) =
      siteReflectConfiguration σ 0
        (diagonalReflectConfiguration τ σ k A) := by
  simp [antiDiagonalReflectConfiguration]

namespace LocalObservable

/-- Anti-linear reflection of an observable through `x τ + x σ = k`. -/
def antiDiagonalTheta (τ σ : Fin d) (k : ℤ) (F : LocalObservable d G) :
    LocalObservable d G :=
  ((F.siteTheta σ 0).diagonalTheta τ σ k).siteTheta σ 0

@[simp]
theorem antiDiagonalTheta_apply (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    F.antiDiagonalTheta τ σ k A =
      star (F (antiDiagonalReflectConfiguration τ σ k A)) := by
  simp [antiDiagonalTheta, antiDiagonalReflectConfiguration]

/-- The local integrand in an anti-diagonal reflection pairing. -/
def antiDiagonalReflectionProduct (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : LocalObservable d G :=
  (F.antiDiagonalTheta τ σ k).mul H

@[simp]
theorem antiDiagonalReflectionProduct_apply (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) (A : Configuration d G) :
    F.antiDiagonalReflectionProduct τ σ k H A =
      star (F (antiDiagonalReflectConfiguration τ σ k A)) * H A := by
  change F.antiDiagonalTheta τ σ k A * H A = _
  rw [antiDiagonalTheta_apply]

/-- Pulling an anti-diagonal reflected product through the coordinate flip
turns it pointwise into the ordinary diagonal reflected product of the
pulled-back observables. -/
theorem antiDiagonalReflectionProduct_siteReflectionPullback_apply
    (τ σ : Fin d) (k : ℤ) (F H : LocalObservable d G)
    (A : Configuration d G) :
    (F.antiDiagonalReflectionProduct τ σ k H).siteReflectionPullback σ 0 A =
      (F.siteReflectionPullback σ 0).diagonalReflectionProduct τ σ k
        (H.siteReflectionPullback σ 0) A := by
  simp [antiDiagonalReflectionProduct_apply,
    diagonalReflectionProduct_apply]

/-- Geometric positive algebra for the anti-diagonal plane
`x τ + x σ = k`. -/
def SupportedInAntiDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) : Prop :=
  ∀ e ∈ F.support,
    k ≤ e.source τ + e.source σ ∧ k ≤ e.target τ + e.target σ

/-- The coordinate flip sends anti-diagonal-positive support to the existing
diagonal-positive support. -/
theorem SupportedInAntiDiagonalPositiveHalf.siteReflectionPullback
    {τ σ : Fin d} (hτσ : τ ≠ σ) {k : ℤ} {F : LocalObservable d G}
    (hF : F.SupportedInAntiDiagonalPositiveHalf τ σ k) :
    (F.siteReflectionPullback σ 0).SupportedInDiagonalPositiveHalf τ σ k := by
  intro e he
  change e ∈ F.support.image (PositiveEdge.siteReflect σ 0) at he
  rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
  rcases PositiveEdge.siteReflect_endpoints σ 0 e₀ with hend | hend
  · rw [hend.1, hend.2,
      siteReflection_diagonalDifference_eq_sum hτσ,
      siteReflection_diagonalDifference_eq_sum hτσ]
    exact hF e₀ he₀
  · rw [hend.1, hend.2,
      siteReflection_diagonalDifference_eq_sum hτσ,
      siteReflection_diagonalDifference_eq_sum hτσ]
    exact (hF e₀ he₀).symm

end LocalObservable

end

end YangMills.Gauge
