/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.AntiDiagonalFamily
import GluelumpPerimeterLaw.Propagation.AntiDiagonalClosingCore
import GluelumpPerimeterLaw.Upstream.Wilson.Loop

/-!
# Matrix observable for the anti-diagonal closing step

The second corner must retain both representation indices.  Here the
transport `rho(Q_p)` is exposed as a flattened family of scalar local
observables.  Its anti-diagonal reflection norm is identified pointwise with
the representation dimension times the normalized Wilson loop around the
reflected closure of `p`.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory Gauge Lattice.Cubic Wilson StrongCoupling
open scoped Matrix BigOperators

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [T2Space G] [GaugeHaarProbability G]

omit [T2Space G] [GaugeHaarProbability G] in
/-- Integrated mixed matrix/rank-one identity. -/
theorem antiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_rankOne_eq
    (μ : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : Endpoint.LocalField d G (Fin n → ℂ))
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection τ σ k x = x)
    (hy : antiDiagonalReflection τ σ k y = y) :
    antiDiagonalReflectionFamilyPairing (μ : Measure (Configuration d G))
        τ σ k (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
        (fun a => (Endpoint.rankOneFlattened Phi Psi).component a) =
      ∫ A, Endpoint.screenedObservable rho Phi Psi
        (antiDiagonalReflectedPathFixed hτσ k p hx hy) A ∂μ := by
  unfold antiDiagonalReflectionFamilyPairing antiDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun A =>
      conjugateHolonomyMatrix_rankOne_antiDiagonalFamilyProduct_apply
        rho Phi Psi hτσ k p hx hy A
  · intro a _ha
    exact integrable_localObservable μ
      ((conjugateHolonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        τ σ k
          ((Endpoint.rankOneFlattened Phi Psi).component a))

omit [T2Space G] [GaugeHaarProbability G] in
/-- Integrated matrix self-pairing/Wilson-loop identity, including the exact
dimension factor from the unnormalized trace. -/
theorem antiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_self_eq
    (μ : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection τ σ k x = x)
    (hy : antiDiagonalReflection τ σ k y = y) :
    antiDiagonalReflectionFamilyPairing (μ : Measure (Configuration d G))
        τ σ k (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
        (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a) =
      (n : ℂ) * ∫ A, rho.wilsonLoop
        ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p).reverse
        A ∂μ := by
  unfold antiDiagonalReflectionFamilyPairing antiDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun A =>
      conjugateHolonomyMatrix_antiDiagonalFamilySelfProduct_apply
        rho hτσ k p hx hy A
  · intro a _ha
    exact integrable_localObservable μ
      ((conjugateHolonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        τ σ k
          (conjugateHolonomyMatrixFlattenedComponent rho p a))

/-- The paper's second corner Cauchy--Schwarz inequality for an arbitrary path
whose endpoints lie on the anti-diagonal plane.  The left side is the screened
`L` observable obtained from the mixed matrix/rank-one pairing; the right side
is exactly `D` times the Wilson loop around the reflected closure. -/
theorem centeredInfiniteVolume_antiDiagonal_matrixClosing
    (eta : ℕ → Configuration d G)
    {nYM : ℕ} (rhoYM : ContinuousUnitaryRepData G nYM)
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (hbeta : ‖(beta : ℂ)‖ <
      StrongCoupling.latticeStrongCouplingRadius d
        rhoYM.wilsonPotential.bound)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : Endpoint.LocalField d G (Fin n → ℂ))
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection τ σ k x = x)
    (hy : antiDiagonalReflection τ σ k y = y)
    (hp : Endpoint.Path.SupportedInAntiDiagonalPositiveHalf τ σ k p)
    (hPhiSupport : Phi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPsiSupport : Psi.SupportedInAntiDiagonalPositiveHalf τ σ k)
    (hPhiNorm : ∀ A, Endpoint.endpointL2Norm (Phi A) ≤ 1)
    (hPsiNorm : ∀ A, Endpoint.endpointL2Norm (Psi A) ≤ 1) :
    Complex.normSq (∫ A, Endpoint.screenedObservable rho Phi Psi
        (antiDiagonalReflectedPathFixed hτσ k p hx hy) A
      ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) ≤
      (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
        ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p) A
      ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) := by
  let μp := centeredInfiniteVolumeProbability
    eta rhoYM.wilsonPotential beta hbeta
  have hmatrixSupport : ∀ a,
      LocalObservable.SupportedInAntiDiagonalPositiveHalf τ σ k
        (conjugateHolonomyMatrixFlattenedComponent rho p a) := fun a =>
    conjugateHolonomyMatrixFlattenedComponent_supportedInAntiDiagonalPositiveHalf
      rho p τ σ k hp a
  have hcs :=
    centeredInfiniteVolume_antiDiagonalReflectionFamily_rankOneComparison
      eta rhoYM beta hbeta0 hbeta hτσ k
      (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
      Phi Psi hmatrixSupport hPhiSupport hPsiSupport hPhiNorm hPsiNorm
  have hmixed :=
    antiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_rankOne_eq
      μp rho Phi Psi hτσ k p hx hy
  have hself :=
    antiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_self_eq
      μp rho hτσ k p hx hy
  rw [show (μp : Measure (Configuration d G)) =
      centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta by
        rfl] at hmixed hself
  have hreverseIntegral :
      (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p).reverse
          A
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) =
        star (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p) A
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) := by
    calc
      _ = ∫ A, star (rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p) A)
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta := by
          apply integral_congr_ae
          exact ae_of_all _ fun A =>
            rho.wilsonLoop_reverse
              ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p) A
      _ = _ := integral_conj
  rw [← hmixed]
  calc
    Complex.normSq (antiDiagonalReflectionFamilyPairing
        (centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta)
        τ σ k (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
        (fun a => (Endpoint.rankOneFlattened Phi Psi).component a)) ≤
        ∑ a, Complex.re (antiDiagonalReflectionPairing
          (centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta)
          τ σ k (conjugateHolonomyMatrixFlattenedComponent rho p a)
          (conjugateHolonomyMatrixFlattenedComponent rho p a)) := hcs
    _ = Complex.re (antiDiagonalReflectionFamilyPairing
          (centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta)
          τ σ k (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
          (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)) := by
      simp [antiDiagonalReflectionFamilyPairing]
    _ = Complex.re ((n : ℂ) * ∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p).reverse
          A
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) :=
      congrArg Complex.re hself
    _ = (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p).reverse
          A
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) := by
      simp
    _ = (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hτσ k p hx hy).reverse.comp p) A
        ∂centeredInfiniteVolumeMeasure eta rhoYM.wilsonPotential beta hbeta) := by
      rw [hreverseIntegral]
      simp

end

end YangMills.Gluelump.Propagation
