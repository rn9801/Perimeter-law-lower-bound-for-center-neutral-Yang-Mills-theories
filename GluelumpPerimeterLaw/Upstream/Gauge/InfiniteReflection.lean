/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.SiteReflection
import YangMills.Gauge.InfiniteReflection

/-! Additive path-level and observable-level reflection operations. -/

namespace YangMills.Lattice.Cubic

/-- Half-integer reflection as a morphism of the cubic-site quiver.  It is
site reflection followed by one positive perpendicular translation. -/
def linkReflectionPrefunctor {d : ℕ} (τ : Fin d) (k : ℤ) : Site d ⥤q Site d :=
  siteReflectionPrefunctor τ k ⋙q translationPrefunctor (unitVector τ)

namespace Path

/-- Reflect every traversed signed edge through a half-integer plane. -/
def linkReflect {d : ℕ} {x y : Site d} (τ : Fin d) (k : ℤ)
    (p : Path x y) :
    Path (linkReflection τ k x) (linkReflection τ k y) :=
  Path.translate (unitVector τ) (Path.siteReflect τ k p)

end Path

/-- The quiver morphism defining link reflection sends the stored edge read
by a signed edge to the canonical stored-edge link reflection. -/
@[simp]
theorem positive_linkReflectionPrefunctor_map {d : ℕ}
    (τ : Fin d) (k : ℤ) {x y : Site d} (e : EdgeBetween x y) :
    ((linkReflectionPrefunctor τ k).map e).1.positive =
      e.1.positive.linkReflect τ k := by
  rcases e with ⟨⟨source, ⟨axis, orientation⟩⟩, hs, ht⟩
  by_cases h : axis = τ
  · subst axis
    cases orientation <;> simp [linkReflectionPrefunctor,
      siteReflectionPrefunctor, translationPrefunctor, Prefunctor.comp,
      SignedEdge.siteReflect, SignedDirection.siteReflect, SignedEdge.translate,
      SignedEdge.positive, PositiveEdge.linkReflect, SignedEdge.target,
      PositiveEdge.target, Lattice.Cubic.translate]
    all_goals ext i; by_cases hi : i = τ
    all_goals simp [linkReflection, Lattice.Cubic.translate, step,
      SignedDirection.delta, SignedDirection.forward, unitVector,
      siteReflection, hi]
    all_goals ring
  · cases orientation <;> simp [linkReflectionPrefunctor,
      siteReflectionPrefunctor, translationPrefunctor, Prefunctor.comp,
      SignedEdge.siteReflect, SignedDirection.siteReflect, SignedEdge.translate,
      SignedEdge.positive, PositiveEdge.linkReflect, SignedEdge.target,
      Lattice.Cubic.translate, h]
    all_goals ext i; by_cases hi : i = τ
    all_goals simp [linkReflection, Lattice.Cubic.translate, step,
      SignedDirection.delta, unitVector, siteReflection, Ne.symm h, hi]

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Holonomy of a half-integer reflected configuration is holonomy along the
reflected path. -/
@[simp]
theorem holonomy_linkReflectConfiguration
    (τ : Fin d) (k : ℤ) (A : Configuration d G)
    {x y : Site d} (p : Lattice.Cubic.Path x y) :
    holonomy (linkReflectConfiguration τ k A) p =
      holonomy A (p.linkReflect τ k) := by
  rw [linkReflectConfiguration_eq_siteReflect_translate,
    holonomy_siteReflectConfiguration,
    holonomy_translateConfiguration]
  rfl

namespace LocalObservable

/-- Linear pullback of a local observable by a site reflection.  This is the
coordinate-change operation underlying conjugation arguments between
different reflection planes; unlike `siteTheta`, it does not conjugate the
observable's value. -/
def siteReflectionPullback (τ : Fin d) (k : ℤ) (F : LocalObservable d G) :
    LocalObservable d G :=
  (F.siteTheta τ k).conj

@[simp]
theorem siteReflectionPullback_apply (τ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    F.siteReflectionPullback τ k A = F (siteReflectConfiguration τ k A) := by
  simp [siteReflectionPullback, LocalObservable.conj]

@[simp]
theorem siteReflectionPullback_siteReflectionPullback_apply
    (τ : Fin d) (k : ℤ) (F : LocalObservable d G)
    (A : Configuration d G) :
    (F.siteReflectionPullback τ k).siteReflectionPullback τ k A = F A := by
  simp

end LocalObservable

end


end YangMills.Gauge
