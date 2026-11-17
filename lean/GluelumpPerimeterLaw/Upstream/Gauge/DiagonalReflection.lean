/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.InfiniteReflection
import YangMills.Gauge.DiagonalReflection

/-! Additive path, gauge-covariance, and observable lemmas for diagonal reflection. -/

namespace YangMills.Lattice.Cubic

/-- Diagonal reflection as a morphism of the cubic-site quiver. -/
def diagonalReflectionPrefunctor {d : ℕ} (τ σ : Fin d)
    (hτσ : τ ≠ σ) (k : ℤ) : Site d ⥤q Site d where
  obj := diagonalReflection τ σ k
  map := fun e =>
    ⟨e.1.diagonalReflect τ σ k,
      by simpa using congrArg (diagonalReflection τ σ k) e.2.1,
      by
        calc
          (e.1.diagonalReflect τ σ k).target =
              diagonalReflection τ σ k e.1.target :=
            SignedEdge.target_diagonalReflect hτσ k e.1
          _ = diagonalReflection τ σ k _ :=
            congrArg (diagonalReflection τ σ k) e.2.2⟩

namespace Path

/-- Reflect every traversed signed edge through an affine diagonal plane. -/
def diagonalReflect {d : ℕ} {x y : Site d} (τ σ : Fin d)
    (hτσ : τ ≠ σ) (k : ℤ) (p : Path x y) :
    Path (diagonalReflection τ σ k x) (diagonalReflection τ σ k y) :=
  (diagonalReflectionPrefunctor τ σ hτσ k).mapPath p

end Path

namespace SignedEdge

@[simp]
theorem positive_diagonalReflect {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (e : SignedEdge d) :
    (e.diagonalReflect τ σ k).positive =
      e.positive.diagonalReflect τ σ k := by
  rcases e with ⟨x, ⟨i, o⟩⟩
  cases o
  · rfl
  · simp only [SignedEdge.diagonalReflect,
      SignedDirection.diagonalReflect, SignedEdge.positive,
      PositiveEdge.diagonalReflect, SignedEdge.target]
    congr 1
    exact (diagonalReflection_step hτσ k x (.backward i)).symm

end SignedEdge

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem signedEdgeValue_diagonalReflectConfiguration {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G) (e : SignedEdge d) :
    signedEdgeValue (diagonalReflectConfiguration τ σ k A) e =
      signedEdgeValue A (e.diagonalReflect τ σ k) := by
  rcases e with ⟨x, ⟨i, o⟩⟩
  cases o
  · rfl
  · simp only [signedEdgeValue, diagonalReflectConfiguration,
      SignedEdge.diagonalReflect, SignedDirection.diagonalReflect,
      SignedEdge.target, PositiveEdge.diagonalReflect]
    rw [diagonalReflection_step hτσ]
    simp [SignedDirection.diagonalReflect]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Holonomy of a diagonally reflected configuration is holonomy along the
reflected path. -/
@[simp]
theorem holonomy_diagonalReflectConfiguration_path {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G)
    {x y : Site d} (p : Lattice.Cubic.Path x y) :
    holonomy (diagonalReflectConfiguration τ σ k A) p =
      holonomy A (p.diagonalReflect τ σ hτσ k) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [holonomy_cons, ih,
        signedEdgeValue_diagonalReflectConfiguration hτσ]
      rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Diagonal reflection transports a gauge transformation by reflecting its
site argument. -/
theorem diagonalReflectConfiguration_gaugeTransform
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (g : GaugeTransformation d G) (A : Configuration d G) :
    diagonalReflectConfiguration τ σ k (gaugeTransform g A) =
      gaugeTransform (fun x => g (diagonalReflection τ σ k x))
        (diagonalReflectConfiguration τ σ k A) := by
  funext e
  simp only [diagonalReflectConfiguration, gaugeTransform_apply,
    PositiveEdge.source_diagonalReflect,
    PositiveEdge.target_diagonalReflect hτσ]

namespace LocalObservable

/-- Linear pullback of a local observable by a coordinate-diagonal
reflection.  This is the measure-symmetry operation; unlike
`diagonalTheta`, it does not conjugate the observable's value. -/
def diagonalReflectionPullback (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) : LocalObservable d G :=
  (F.diagonalTheta τ σ k).conj

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalReflectionPullback_apply (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    F.diagonalReflectionPullback τ σ k A =
      F (diagonalReflectConfiguration τ σ k A) := by
  simp [diagonalReflectionPullback, LocalObservable.conj]

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalReflectionPullback_diagonalReflectionPullback_apply
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    (F.diagonalReflectionPullback τ σ k).diagonalReflectionPullback τ σ k A =
      F A := by
  simp [hτσ]

omit [Group G] [IsTopologicalGroup G] in
/-- The diagonal-positive local algebra is closed under multiplication. -/
theorem SupportedInDiagonalPositiveHalf.mul {τ σ : Fin d} {k : ℤ}
    {F H : LocalObservable d G}
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (hH : H.SupportedInDiagonalPositiveHalf τ σ k) :
    (F.mul H).SupportedInDiagonalPositiveHalf τ σ k := by
  intro e he
  change e ∈ F.support ∪ H.support at he
  rcases Finset.mem_union.mp he with he | he
  · exact hF e he
  · exact hH e he

end LocalObservable

end


end YangMills.Gauge
