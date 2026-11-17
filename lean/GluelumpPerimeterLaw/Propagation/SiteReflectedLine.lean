/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Reflection
import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState

/-!
# Site-reflected screened lines

This file is the integer-plane counterpart of the crossing-link reflected-line
bridge.  A positive half-path begins at a site fixed by the reflection.  Its
reflected reverse and the original half-path form a full screened line.  At
the fixed cutting site, the screened contraction is exactly a finite sum of
site-reflection pairings of the outgoing half-line components.

The construction is pointwise and measure independent.  In particular it
does not mention a Gibbs action, a thermodynamic limit, or strong coupling.
-/

namespace YangMills.Gluelump.Propagation

open MeasureTheory
open MeasureTheory Gauge Lattice.Cubic Wilson Endpoint

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- A site on the plane `x τ = k` is fixed by the corresponding site
reflection. -/
theorem siteReflection_eq_self_of_apply_eq
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k) :
    siteReflection τ k z = z := by
  ext i
  by_cases hi : i = τ
  · subst i
    simp [siteReflection, hz]
    omega
  · simp [siteReflection, hi]

/-- The reflected reverse of a positive half-path, with its endpoint on the
reflection plane cast back to the original cutting site. -/
def siteReflectedIncomingPath
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y) :
    Lattice.Cubic.Path (siteReflection τ k y) z :=
  YangMills.Basic.OrientedPath.castTarget
    (q.siteReflect τ k).reverse
    (siteReflection_eq_self_of_apply_eq τ k z hz)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem holonomy_siteReflectedIncomingPath
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y)
    (A : Configuration d G) :
    holonomy A (siteReflectedIncomingPath τ k z hz q) =
      (holonomy (siteReflectConfiguration τ k A) q)⁻¹ := by
  unfold siteReflectedIncomingPath
  rw [holonomy_castTarget, holonomy_reverse,
    holonomy_siteReflectConfiguration]

/-- Join the reflected reverse of one positive half-path to a second positive
half-path at their common site-reflection cut. -/
def siteReflectedMixedFullPath
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d} (q : Lattice.Cubic.Path z y)
    (r : Lattice.Cubic.Path z u) :
    Lattice.Cubic.Path (siteReflection τ k y) u :=
  (siteReflectedIncomingPath τ k z hz q).comp r

/-- Site-reflection self-closure of one positive half-path. -/
def siteReflectedFullPath
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y) :
    Lattice.Cubic.Path (siteReflection τ k y) y :=
  siteReflectedMixedFullPath τ k z hz q q

/-- Screened contraction of two possibly different site-positive halves. -/
def siteReflectedMixedObservable
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d} (q : Lattice.Cubic.Path z y)
    (r : Lattice.Cubic.Path z u) : LocalObservable d G :=
  screenedObservable rho (Phi.sitePullback τ k) Psi
    (siteReflectedMixedFullPath τ k z hz q r)

/-- The site-reflected norm-square line associated with one positive half. -/
def siteReflectedObservable
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y) : LocalObservable d G :=
  siteReflectedMixedObservable rho Phi Phi τ k z hz q q

/-- Reflection turns the incoming component of the reflected half-path into
the outgoing component of the original half-path. -/
theorem incomingHalfComponent_siteReflectedIncomingPath_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y) (i : Fin n)
    (A : Configuration d G) :
    incomingHalfComponent rho (Phi.sitePullback τ k)
        (siteReflectedIncomingPath τ k z hz q) i A =
      outgoingHalfComponent rho Phi q i
        (siteReflectConfiguration τ k A) := by
  simp only [incomingHalfComponent_apply, outgoingHalfComponent_apply,
    LocalField.sitePullback_apply,
    holonomy_siteReflectedIncomingPath, inv_inv]

/-- Exact finite-family site-reflection pairing for a mixed screened line. -/
theorem siteReflectedMixedObservable_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d} (q : Lattice.Cubic.Path z y)
    (r : Lattice.Cubic.Path z u) (A : Configuration d G) :
    siteReflectedMixedObservable rho Phi Psi τ k z hz q r A =
      ∑ i, (outgoingHalfComponent rho Phi q i).siteReflectionProduct
        τ k (outgoingHalfComponent rho Psi r i) A := by
  rw [siteReflectedMixedObservable, screenedObservable_apply]
  unfold siteReflectedMixedFullPath
  rw [screenedValue_comp_eq_halfGram]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [incomingHalfComponent_siteReflectedIncomingPath_apply]
  rfl

/-- Exact finite-family norm-square formula for a self-reflected screened
line. -/
theorem siteReflectedObservable_apply
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y)
    (A : Configuration d G) :
    siteReflectedObservable rho Phi τ k z hz q A =
      ∑ i, (outgoingHalfComponent rho Phi q i).siteReflectionProduct
        τ k (outgoingHalfComponent rho Phi q i) A := by
  exact siteReflectedMixedObservable_apply rho Phi Phi τ k z hz q q A

/-- Positive support of an endpoint and its half-path gives positive support
of every scalar outgoing half-line component. -/
theorem outgoingHalfComponent_supportedInSitePositiveHalf
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    {τ : Fin d} {k : ℤ} {z y : Site d}
    (q : Lattice.Cubic.Path z y)
    (hPhi : Phi.SupportedInSitePositiveHalf τ k)
    (hq : Endpoint.Path.SupportedInSitePositiveHalf τ k q)
    (i : Fin n) :
    (outgoingHalfComponent rho Phi q i).SupportedInSitePositiveHalf τ k := by
  change Endpoint.EdgeSet.SupportedInSitePositiveHalf τ k
    (Phi.support ∪ q.edgeSupport)
  exact Endpoint.EdgeSet.site_union hPhi hq

section Measure

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

omit [Group G] [IsTopologicalGroup G] [T2Space G] in
private theorem integrableLocalObservable
    (mu : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) :
    MeasureTheory.Integrable F (mu : MeasureTheory.Measure (Configuration d G)) := by
  apply MeasureTheory.Integrable.of_bound
    F.toContinuousMap.continuous.measurable.aestronglyMeasurable
    ‖F.toBoundedContinuousMap‖
  exact ae_of_all _ F.norm_apply_le

/-- Integration of a site-reflected screened line is exactly the neutral
finite-family reflection pairing. -/
theorem integral_siteReflectedMixedObservable_eq_familyPairing
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d} (q : Lattice.Cubic.Path z y)
    (r : Lattice.Cubic.Path z u) :
    (∫ A, siteReflectedMixedObservable rho Phi Psi τ k z hz q r A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) =
      measureSiteReflectionFamilyPairing
        (mu : MeasureTheory.Measure (Configuration d G)) τ k
        (fun i ↦ outgoingHalfComponent rho Phi q i)
        (fun i ↦ outgoingHalfComponent rho Psi r i) := by
  unfold measureSiteReflectionFamilyPairing measureSiteReflectionPairing
  rw [← MeasureTheory.integral_finsetSum]
  · apply MeasureTheory.integral_congr_ae
    exact ae_of_all _ fun A ↦
      siteReflectedMixedObservable_apply rho Phi Psi τ k z hz q r A
  · intro i _hi
    exact integrableLocalObservable mu
      ((outgoingHalfComponent rho Phi q i).siteReflectionProduct τ k
        (outgoingHalfComponent rho Psi r i))

/-- Self-pairing specialization of
`integral_siteReflectedMixedObservable_eq_familyPairing`. -/
theorem integral_siteReflectedObservable_eq_familyPairing
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y) :
    (∫ A, siteReflectedObservable rho Phi τ k z hz q A
        ∂(mu : Measure (Configuration d G))) =
      measureSiteReflectionFamilyPairing
        (mu : Measure (Configuration d G)) τ k
        (fun i ↦ outgoingHalfComponent rho Phi q i)
        (fun i ↦ outgoingHalfComponent rho Phi q i) := by
  exact integral_siteReflectedMixedObservable_eq_familyPairing
    mu rho Phi Phi τ k z hz q q

/-- A neutral reflection-positive state makes every site-reflected screened
self-line real and nonnegative. -/
theorem ReflectionPositiveState.siteReflectedObservable_positive
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (Phi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y : Site d} (q : Lattice.Cubic.Path z y)
    (hPhi : Phi.SupportedInSitePositiveHalf τ k)
    (hq : Endpoint.Path.SupportedInSitePositiveHalf τ k q) :
    Complex.im (∫ A, siteReflectedObservable rho Phi τ k z hz q A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) = 0 ∧
      0 ≤ Complex.re (∫ A, siteReflectedObservable rho Phi τ k z hz q A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) := by
  rw [integral_siteReflectedObservable_eq_familyPairing]
  exact hstate.siteFamilyPositive τ k
    (fun i ↦ outgoingHalfComponent rho Phi q i)
    (fun i ↦ outgoingHalfComponent_supportedInSitePositiveHalf
      rho Phi q hPhi hq i)

/-- Finite-family site-reflection Cauchy--Schwarz for two screened halves. -/
theorem ReflectionPositiveState.siteReflectedMixed_cauchySchwarz
    {mu : ProbabilityMeasure (Configuration d G)}
    (hstate : ReflectionPositiveState mu)
    (rho : ContinuousUnitaryRepData G n)
    (Phi Psi : LocalField d G (Fin n → ℂ))
    (τ : Fin d) (k : ℤ) (z : Site d) (hz : z τ = k)
    {y u : Site d} (q : Lattice.Cubic.Path z y)
    (r : Lattice.Cubic.Path z u)
    (hPhi : Phi.SupportedInSitePositiveHalf τ k)
    (hPsi : Psi.SupportedInSitePositiveHalf τ k)
    (hq : Endpoint.Path.SupportedInSitePositiveHalf τ k q)
    (hr : Endpoint.Path.SupportedInSitePositiveHalf τ k r) :
    Complex.normSq (∫ A,
        siteReflectedMixedObservable rho Phi Psi τ k z hz q r A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) ≤
      Complex.re (∫ A, siteReflectedObservable rho Phi τ k z hz q A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) *
      Complex.re (∫ A, siteReflectedObservable rho Psi τ k z hz r A
        ∂(mu : MeasureTheory.Measure (Configuration d G))) := by
  have hcs := hstate.siteFamilyCauchySchwarz τ k
    (fun i ↦ outgoingHalfComponent rho Phi q i)
    (fun i ↦ outgoingHalfComponent rho Psi r i)
    (fun i ↦ outgoingHalfComponent_supportedInSitePositiveHalf
      rho Phi q hPhi hq i)
    (fun i ↦ outgoingHalfComponent_supportedInSitePositiveHalf
      rho Psi r hPsi hr i)
  rw [integral_siteReflectedMixedObservable_eq_familyPairing,
    integral_siteReflectedObservable_eq_familyPairing,
    integral_siteReflectedObservable_eq_familyPairing]
  have hrePhi : Complex.re (measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) τ k
      (fun i ↦ outgoingHalfComponent rho Phi q i)
      (fun i ↦ outgoingHalfComponent rho Phi q i)) =
      ∑ i, Complex.re (measureSiteReflectionPairing
        (mu : Measure (Configuration d G)) τ k
        (outgoingHalfComponent rho Phi q i)
        (outgoingHalfComponent rho Phi q i)) := by
    unfold measureSiteReflectionFamilyPairing
    change Complex.reAddGroupHom ( ∑ i, measureSiteReflectionPairing
      (mu : Measure (Configuration d G)) τ k
      (outgoingHalfComponent rho Phi q i)
      (outgoingHalfComponent rho Phi q i)) = _
    rw [map_sum]
    rfl
  have hrePsi : Complex.re (measureSiteReflectionFamilyPairing
      (mu : Measure (Configuration d G)) τ k
      (fun i ↦ outgoingHalfComponent rho Psi r i)
      (fun i ↦ outgoingHalfComponent rho Psi r i)) =
      ∑ i, Complex.re (measureSiteReflectionPairing
        (mu : Measure (Configuration d G)) τ k
        (outgoingHalfComponent rho Psi r i)
        (outgoingHalfComponent rho Psi r i)) := by
    unfold measureSiteReflectionFamilyPairing
    change Complex.reAddGroupHom ( ∑ i, measureSiteReflectionPairing
      (mu : Measure (Configuration d G)) τ k
      (outgoingHalfComponent rho Psi r i)
      (outgoingHalfComponent rho Psi r i)) = _
    rw [map_sum]
    rfl
  rw [hrePhi, hrePsi]
  exact hcs

end Measure

end

end YangMills.Gluelump.Propagation
