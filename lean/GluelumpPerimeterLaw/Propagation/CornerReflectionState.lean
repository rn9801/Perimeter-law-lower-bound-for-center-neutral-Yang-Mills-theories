/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState
import GluelumpPerimeterLaw.Propagation.AntiDiagonalClosingCore
import GluelumpPerimeterLaw.Propagation.DiagonalBendingCore

/-!
# Corner reflection inequalities for a neutral probability state

The pointwise row-vector bend and matrix-family close are converted here into
measure-parametric inequalities over `Gauge.ReflectionPositiveState`.  This is
the analytic corner layer shared by direct endpoint geometries; it has no
strong-coupling or thermodynamic-limit dependency.
-/

open MeasureTheory

namespace YangMills.Gluelump.Propagation

open Gauge Lattice.Cubic Wilson Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [Group G] [IsTopologicalGroup G] [T2Space G] in
private theorem integrableLocalObservable
    (mu : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) :
    Integrable F (mu : Measure (Configuration d G)) := by
  apply Integrable.of_bound
    F.toContinuousMap.continuous.measurable.aestronglyMeasurable
    ‖F.toBoundedContinuousMap‖
  exact ae_of_all _ F.norm_apply_le

/-! ## Diagonal row bending -/

/-- Integrated mixed row/endpoint identity for the neutral measure pairing. -/
theorem measureDiagonalReflectionFamilyPairing_incoming_endpoint_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi Xi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z) :
    measureDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k
        (fun i => incomingHalfComponent rho Phi p i)
        (fun i => Xi.component i) =
      ∫ A, screenedObservable rho (Phi.diagonalPullback tau sigma k) Xi
        (diagonalReflectedPathToFixed hts k p hz) A ∂mu := by
  unfold measureDiagonalReflectionFamilyPairing
    measureDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun A =>
      diagonalIncoming_endpoint_familyProduct_apply
        rho Phi Xi hts k p hz A
  · intro i _hi
    exact integrableLocalObservable mu
      ((incomingHalfComponent rho Phi p i).diagonalReflectionProduct
        tau sigma k (Xi.component i))

/-- Swapping the two diagonal-family arguments gives the screened segment
with the comparison endpoint reflected back and the arm reversed. -/
theorem measureDiagonalReflectionFamilyPairing_endpoint_incoming_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi Xi : LocalField d G (Fin n → ℂ))
    (tau sigma : Fin d) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z) :
    measureDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k
        (fun i => Xi.component i)
        (fun i => incomingHalfComponent rho Phi p i) =
      ∫ A, screenedObservable rho (Xi.diagonalPullback tau sigma k) Phi
        p.reverse A ∂mu := by
  unfold measureDiagonalReflectionFamilyPairing
    measureDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun A => by
      simp only [LocalObservable.diagonalReflectionProduct_apply,
        LocalField.component_apply, LocalField.diagonalPullback_apply,
        incomingHalfComponent_apply, screenedObservable_apply,
        screenedValue, holonomy_reverse]
  · intro i _hi
    exact integrableLocalObservable mu
      ((Xi.component i).diagonalReflectionProduct tau sigma k
        (incomingHalfComponent rho Phi p i))

/-- Integrated row self-pairing/L-shape identity for the neutral measure. -/
theorem measureDiagonalReflectionFamilyPairing_incoming_self_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z) :
    measureDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k
        (fun i => incomingHalfComponent rho Phi p i)
        (fun i => incomingHalfComponent rho Phi p i) =
      ∫ A, screenedObservable rho (Phi.diagonalPullback tau sigma k) Phi
        ((diagonalReflectedPathToFixed hts k p hz).comp p.reverse) A ∂mu := by
  unfold measureDiagonalReflectionFamilyPairing
    measureDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun A =>
      diagonalIncoming_familySelfProduct_apply rho Phi hts k p hz A
  · intro i _hi
    exact integrableLocalObservable mu
      ((incomingHalfComponent rho Phi p i).diagonalReflectionProduct
        tau sigma k (incomingHalfComponent rho Phi p i))

/-- The diagonal reflection norm of a pointwise normalized endpoint-coordinate
family is at most one. -/
theorem endpointComponentFamily_measureDiagonalSelfPairing_re_le_one
    (mu : ProbabilityMeasure (Configuration d G))
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : ∀ A, endpointL2Norm (Phi A) ≤ 1)
    (tau sigma : Fin d) (k : ℤ) :
    Complex.re (measureDiagonalReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau sigma k
      (fun i => Phi.component i) (fun i => Phi.component i)) ≤ 1 := by
  have hintegrable : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun A =>
        (Phi.component i).diagonalReflectionProduct tau sigma k
          (Phi.component i) A) (mu : Measure (Configuration d G)) := by
    intro i _hi
    exact integrableLocalObservable mu
      ((Phi.component i).diagonalReflectionProduct tau sigma k
        (Phi.component i))
  have hpairing :
      measureDiagonalReflectionFamilyPairing
          (mu : Measure (Configuration d G)) tau sigma k
          (fun i => Phi.component i) (fun i => Phi.component i) =
        ∫ A, hermitianPairing
          (Phi (diagonalReflectConfiguration tau sigma k A)) (Phi A) ∂mu := by
    unfold measureDiagonalReflectionFamilyPairing
      measureDiagonalReflectionPairing
    rw [← integral_finsetSum Finset.univ hintegrable]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => rfl
  rw [hpairing]
  calc
    Complex.re (∫ A, hermitianPairing
        (Phi (diagonalReflectConfiguration tau sigma k A)) (Phi A) ∂mu) ≤
        ‖∫ A, hermitianPairing
          (Phi (diagonalReflectConfiguration tau sigma k A)) (Phi A) ∂mu‖ :=
      Complex.re_le_norm _
    _ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (mu : Measure (Configuration d G))) (C := (1 : ℝ)) <|
          ae_of_all _ fun A => by
            calc
              ‖hermitianPairing
                  (Phi (diagonalReflectConfiguration tau sigma k A))
                  (Phi A)‖ ≤
                  endpointL2Norm
                      (Phi (diagonalReflectConfiguration tau sigma k A)) *
                    endpointL2Norm (Phi A) :=
                norm_hermitianPairing_le _ _
              _ ≤ 1 * 1 := mul_le_mul
                (hPhi (diagonalReflectConfiguration tau sigma k A)) (hPhi A)
                (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1

/-- The paper's first corner Cauchy--Schwarz step over an arbitrary neutral
reflection-positive probability state. -/
theorem Gauge.ReflectionPositiveState.diagonalRowBending
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : Gauge.ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Xi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z)
    (hPhi : Phi.SupportedInDiagonalPositiveHalf tau sigma k)
    (hp : Endpoint.Path.SupportedInDiagonalPositiveHalf tau sigma k p)
    (hXi : Xi.SupportedInDiagonalPositiveHalf tau sigma k)
    (hXiNorm : ∀ A, endpointL2Norm (Xi A) ≤ 1) :
    Complex.normSq (∫ A,
        screenedObservable rho (Phi.diagonalPullback tau sigma k) Xi
          (diagonalReflectedPathToFixed hts k p hz) A ∂mu) ≤
      Complex.re (∫ A,
        screenedObservable rho (Phi.diagonalPullback tau sigma k) Phi
          ((diagonalReflectedPathToFixed hts k p hz).comp p.reverse) A
        ∂mu) := by
  let F : Fin n → LocalObservable d G :=
    fun i => incomingHalfComponent rho Phi p i
  let H : Fin n → LocalObservable d G := fun i => Xi.component i
  have hF : ∀ i, (F i).SupportedInDiagonalPositiveHalf tau sigma k :=
    fun i => incomingHalfComponent_supportedInDiagonalPositiveHalf
      rho Phi p i tau sigma k hPhi hp
  have hH : ∀ i, (H i).SupportedInDiagonalPositiveHalf tau sigma k := by
    intro i e he
    exact hXi e he
  have hcs := hstate.diagonalFamilyCauchySchwarz hts k F H hF hH
  have hFnonneg := (hstate.diagonalFamilyPositive hts k F hF).2
  have hHone : Complex.re (measureDiagonalReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau sigma k H H) ≤ 1 :=
    endpointComponentFamily_measureDiagonalSelfPairing_re_le_one
      mu Xi hXiNorm tau sigma k
  have hproduct :
      (∑ i, Complex.re (measureDiagonalReflectionPairing
        (mu : Measure (Configuration d G)) tau sigma k (F i) (F i))) *
          ∑ i, Complex.re (measureDiagonalReflectionPairing
            (mu : Measure (Configuration d G)) tau sigma k (H i) (H i)) ≤
        ∑ i, Complex.re (measureDiagonalReflectionPairing
          (mu : Measure (Configuration d G)) tau sigma k (F i) (F i)) := by
    apply mul_le_of_le_one_right
    · simpa [measureDiagonalReflectionFamilyPairing] using hFnonneg
    · simpa [measureDiagonalReflectionFamilyPairing] using hHone
  have hmixed := measureDiagonalReflectionFamilyPairing_incoming_endpoint_eq
    mu rho Phi Xi hts k p hz
  have hself := measureDiagonalReflectionFamilyPairing_incoming_self_eq
    mu rho Phi hts k p hz
  rw [← hmixed, ← hself]
  exact hcs.trans (by
    simpa [F, H, measureDiagonalReflectionFamilyPairing] using hproduct)

/-- Diagonal Hermitian symmetry identifies the reflected mixed row with the
complex conjugate of the original, oppositely oriented straight segment.
This is the neutral substitute for assuming diagonal invariance of the whole
measure. -/
theorem Gauge.ReflectionPositiveState.diagonalBentIntegral_eq_star_reverse
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : Gauge.ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Xi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x z : Site d} (p : Lattice.Cubic.Path x z)
    (hz : diagonalReflection tau sigma k z = z)
    (hPhi : Phi.SupportedInDiagonalPositiveHalf tau sigma k)
    (hp : Endpoint.Path.SupportedInDiagonalPositiveHalf tau sigma k p)
    (hXi : Xi.SupportedInDiagonalPositiveHalf tau sigma k) :
    (∫ A, screenedObservable rho (Phi.diagonalPullback tau sigma k) Xi
        (diagonalReflectedPathToFixed hts k p hz) A ∂mu) =
      star (∫ A, screenedObservable rho
        (Xi.diagonalPullback tau sigma k) Phi p.reverse A ∂mu) := by
  let F : Fin n → LocalObservable d G :=
    fun i => incomingHalfComponent rho Phi p i
  let H : Fin n → LocalObservable d G := fun i => Xi.component i
  have hF : ∀ i, (F i).SupportedInDiagonalPositiveHalf tau sigma k :=
    fun i => incomingHalfComponent_supportedInDiagonalPositiveHalf
      rho Phi p i tau sigma k hPhi hp
  have hH : ∀ i, (H i).SupportedInDiagonalPositiveHalf tau sigma k := by
    intro i e he
    exact hXi e he
  have hherm :
      star (measureDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k H F) =
      measureDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k F H := by
    unfold measureDiagonalReflectionFamilyPairing
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    exact hstate.diagonalHermitian tau sigma k hts (F i) (H i)
      (hF i) (hH i)
  have hmixed := measureDiagonalReflectionFamilyPairing_incoming_endpoint_eq
    mu rho Phi Xi hts k p hz
  have hreverse := measureDiagonalReflectionFamilyPairing_endpoint_incoming_eq
    mu rho Phi Xi tau sigma k p
  calc
    _ = measureDiagonalReflectionFamilyPairing
          (mu : Measure (Configuration d G)) tau sigma k F H := hmixed.symm
    _ = star (measureDiagonalReflectionFamilyPairing
          (mu : Measure (Configuration d G)) tau sigma k H F) := hherm.symm
    _ = _ := congrArg star hreverse

/-! ## Anti-diagonal matrix closing -/

/-- Integrated mixed matrix/rank-one identity for the neutral measure
pairing. -/
theorem measureAntiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_rankOne_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y) :
    measureAntiDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k
        (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
        (fun a => (rankOneFlattened Phi Psi).component a) =
      ∫ A, screenedObservable rho Phi Psi
        (antiDiagonalReflectedPathFixed hts k p hx hy) A ∂mu := by
  unfold measureAntiDiagonalReflectionFamilyPairing
    measureAntiDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun A =>
      conjugateHolonomyMatrix_rankOne_antiDiagonalFamilyProduct_apply
        rho Phi Psi hts k p hx hy A
  · intro a _ha
    exact integrableLocalObservable mu
      ((conjugateHolonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        tau sigma k
          ((rankOneFlattened Phi Psi).component a))

/-- Integrated matrix self-pairing/Wilson-loop identity, including the exact
dimension factor from the unnormalized character. -/
theorem measureAntiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_self_eq
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y) :
    measureAntiDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k
        (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a)
        (fun a => conjugateHolonomyMatrixFlattenedComponent rho p a) =
      (n : ℂ) * ∫ A, rho.wilsonLoop
        ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p).reverse
        A ∂mu := by
  unfold measureAntiDiagonalReflectionFamilyPairing
    measureAntiDiagonalReflectionPairing
  rw [← integral_finsetSum]
  · rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun A =>
      conjugateHolonomyMatrix_antiDiagonalFamilySelfProduct_apply
        rho hts k p hx hy A
  · intro a _ha
    exact integrableLocalObservable mu
      ((conjugateHolonomyMatrixFlattenedComponent rho p a).antiDiagonalReflectionProduct
        tau sigma k
          (conjugateHolonomyMatrixFlattenedComponent rho p a))

/-- The anti-diagonal reflection norm of a pointwise normalized endpoint
coordinate family is at most one. -/
theorem endpointComponentFamily_measureAntiDiagonalSelfPairing_re_le_one
    (mu : ProbabilityMeasure (Configuration d G))
    (Phi : LocalField d G (Fin n → ℂ))
    (hPhi : ∀ A, endpointL2Norm (Phi A) ≤ 1)
    (tau sigma : Fin d) (k : ℤ) :
    Complex.re (measureAntiDiagonalReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau sigma k
      (fun i => Phi.component i) (fun i => Phi.component i)) ≤ 1 := by
  have hintegrable : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun A =>
        (Phi.component i).antiDiagonalReflectionProduct tau sigma k
          (Phi.component i) A) (mu : Measure (Configuration d G)) := by
    intro i _hi
    exact integrableLocalObservable mu
      ((Phi.component i).antiDiagonalReflectionProduct tau sigma k
        (Phi.component i))
  have hpairing :
      measureAntiDiagonalReflectionFamilyPairing
          (mu : Measure (Configuration d G)) tau sigma k
          (fun i => Phi.component i) (fun i => Phi.component i) =
        ∫ A, hermitianPairing
          (Phi (antiDiagonalReflectConfiguration tau sigma k A)) (Phi A)
          ∂mu := by
    unfold measureAntiDiagonalReflectionFamilyPairing
      measureAntiDiagonalReflectionPairing
    rw [← integral_finsetSum Finset.univ hintegrable]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      simp only [LocalObservable.antiDiagonalReflectionProduct_apply,
        LocalField.component_apply, hermitianPairing]
  rw [hpairing]
  calc
    Complex.re (∫ A, hermitianPairing
        (Phi (antiDiagonalReflectConfiguration tau sigma k A)) (Phi A) ∂mu) ≤
        ‖∫ A, hermitianPairing
          (Phi (antiDiagonalReflectConfiguration tau sigma k A)) (Phi A)
          ∂mu‖ := Complex.re_le_norm _
    _ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (mu : Measure (Configuration d G))) (C := (1 : ℝ)) <|
          ae_of_all _ fun A => by
            calc
              ‖hermitianPairing
                  (Phi (antiDiagonalReflectConfiguration tau sigma k A))
                  (Phi A)‖ ≤
                  endpointL2Norm
                      (Phi (antiDiagonalReflectConfiguration tau sigma k A)) *
                    endpointL2Norm (Phi A) :=
                norm_hermitianPairing_le _ _
              _ ≤ 1 * 1 := mul_le_mul
                (hPhi (antiDiagonalReflectConfiguration tau sigma k A))
                (hPhi A) (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1

/-- The paper's second corner Cauchy--Schwarz step over an arbitrary neutral
reflection-positive probability state. -/
theorem Gauge.ReflectionPositiveState.antiDiagonalMatrixClosing
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : Gauge.ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    {tau sigma : Fin d} (hts : tau ≠ sigma) (k : ℤ)
    {x y : Site d} (p : Lattice.Cubic.Path x y)
    (hx : antiDiagonalReflection tau sigma k x = x)
    (hy : antiDiagonalReflection tau sigma k y = y)
    (hp : Endpoint.Path.SupportedInAntiDiagonalPositiveHalf tau sigma k p)
    (hPhiSupport : Phi.SupportedInAntiDiagonalPositiveHalf tau sigma k)
    (hPsiSupport : Psi.SupportedInAntiDiagonalPositiveHalf tau sigma k)
    (hPhiNorm : ∀ A, endpointL2Norm (Phi A) ≤ 1)
    (hPsiNorm : ∀ A, endpointL2Norm (Psi A) ≤ 1) :
    Complex.normSq (∫ A, screenedObservable rho Phi Psi
        (antiDiagonalReflectedPathFixed hts k p hx hy) A ∂mu) ≤
      (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
        ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A
        ∂mu) := by
  let F : Fin (n * n) → LocalObservable d G := fun a =>
    conjugateHolonomyMatrixFlattenedComponent rho p a
  let H : Fin (n * n) → LocalObservable d G := fun a =>
    (rankOneFlattened Phi Psi).component a
  have hF : ∀ a, (F a).SupportedInAntiDiagonalPositiveHalf tau sigma k :=
    fun a =>
      conjugateHolonomyMatrixFlattenedComponent_supportedInAntiDiagonalPositiveHalf
        rho p tau sigma k hp a
  have hH : ∀ a, (H a).SupportedInAntiDiagonalPositiveHalf tau sigma k :=
    fun a => rankOneFlattened_component_supportedInAntiDiagonalPositiveHalf
      Phi Psi tau sigma k hPhiSupport hPsiSupport a
  have hcs := hstate.antiDiagonalFamilyCauchySchwarz hts k F H hF hH
  have hFnonneg := (hstate.antiDiagonalFamilyPositive hts k F hF).2
  have hHone : Complex.re (measureAntiDiagonalReflectionFamilyPairing
      (mu : Measure (Configuration d G)) tau sigma k H H) ≤ 1 :=
    endpointComponentFamily_measureAntiDiagonalSelfPairing_re_le_one
      mu (rankOneFlattened Phi Psi)
        (endpointL2Norm_rankOneFlattened_le_one
          Phi Psi hPhiNorm hPsiNorm) tau sigma k
  have hproduct :
      (∑ a, Complex.re (measureAntiDiagonalReflectionPairing
        (mu : Measure (Configuration d G)) tau sigma k (F a) (F a))) *
          ∑ a, Complex.re (measureAntiDiagonalReflectionPairing
            (mu : Measure (Configuration d G)) tau sigma k (H a) (H a)) ≤
        ∑ a, Complex.re (measureAntiDiagonalReflectionPairing
          (mu : Measure (Configuration d G)) tau sigma k (F a) (F a)) := by
    apply mul_le_of_le_one_right
    · simpa [measureAntiDiagonalReflectionFamilyPairing] using hFnonneg
    · simpa [measureAntiDiagonalReflectionFamilyPairing] using hHone
  have hmixed :=
    measureAntiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_rankOne_eq
      mu rho Phi Psi hts k p hx hy
  have hself :=
    measureAntiDiagonalReflectionFamilyPairing_conjugateHolonomyMatrix_self_eq
      mu rho hts k p hx hy
  have hreverseIntegral :
      (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p).reverse
          A ∂mu) =
        star (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A
          ∂mu) := by
    calc
      _ = ∫ A, star (rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A)
          ∂mu := by
        apply integral_congr_ae
        exact ae_of_all _ fun A =>
          rho.wilsonLoop_reverse
            ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A
      _ = _ := integral_conj
  rw [← hmixed]
  calc
    Complex.normSq (measureAntiDiagonalReflectionFamilyPairing
        (mu : Measure (Configuration d G)) tau sigma k F H) ≤
        ∑ a, Complex.re (measureAntiDiagonalReflectionPairing
          (mu : Measure (Configuration d G)) tau sigma k (F a) (F a)) :=
      hcs.trans hproduct
    _ = Complex.re (measureAntiDiagonalReflectionFamilyPairing
          (mu : Measure (Configuration d G)) tau sigma k F F) := by
      simp [measureAntiDiagonalReflectionFamilyPairing]
    _ = Complex.re ((n : ℂ) * ∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p).reverse
          A
          ∂mu) := congrArg Complex.re hself
    _ = (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p).reverse
          A ∂mu) := by simp
    _ = (n : ℝ) * Complex.re (∫ A, rho.wilsonLoop
          ((antiDiagonalReflectedPathFixed hts k p hx hy).reverse.comp p) A
          ∂mu) := by rw [hreverseIntegral]; simp

end


end YangMills.Gluelump.Propagation
