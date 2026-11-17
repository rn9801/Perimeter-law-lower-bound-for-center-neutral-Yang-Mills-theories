/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Covariance
import GluelumpPerimeterLaw.Endpoint.LoopFamily
import GluelumpPerimeterLaw.Lie.AxialMap

/-!
# Axial local fields and screening maps

The plaquette axial field is a concrete bounded-range cylindrical field which
transforms by matrix conjugation at its base site.  The final construction is
stated for an arbitrary finite-dimensional source action, so an adjoint tensor
power can be inserted without changing the endpoint or observable APIs.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open scoped Matrix

noncomputable section

variable {d n N : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Covariance of a general source-valued field at one lattice site. -/
def SourceCovariantAt {E : Type*} [TopologicalSpace E]
    (act : G → E → E) (x : Site d) (Xi : LocalField d G E) : Prop :=
  ∀ g A, Xi (gaugeTransform g A) = act (g x) (Xi A)

/-- The matrix axial field carried by one plaquette. -/
def axialPlaquetteField (eta : ContinuousUnitaryRepData G N)
    (p : Plaquette d) :
    LocalField d G (Matrix (Fin N) (Fin N) ℂ) where
  toContinuousMap :=
    ⟨fun A => Lie.axialMatrix eta (holonomy A p.boundary),
      Lie.continuous_axialMatrix eta |>.comp (continuous_holonomy p.boundary)⟩
  support := p.boundary.edgeSupport
  dependsOn_support := by
    intro A B hAB
    change Lie.axialMatrix eta (holonomy A p.boundary) =
      Lie.axialMatrix eta (holonomy B p.boundary)
    rw [holonomy_eq_of_eqOn_edgeSupport p.boundary hAB]

@[simp]
theorem axialPlaquetteField_apply
    (eta : ContinuousUnitaryRepData G N) (p : Plaquette d)
    (A : Configuration d G) :
    axialPlaquetteField eta p A =
      Lie.axialMatrix eta (holonomy A p.boundary) :=
  rfl

/-- A plaquette axial field transforms by conjugation at the plaquette base. -/
theorem axialPlaquetteField_covariant
    (eta : ContinuousUnitaryRepData G N) (p : Plaquette d) :
    SourceCovariantAt
      (fun h X => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * X *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ))
      p.base (axialPlaquetteField eta p) := by
  intro g A
  rw [axialPlaquetteField_apply, axialPlaquetteField_apply,
    holonomy_loop_gaugeTransform]
  exact Lie.axialMatrix_conj eta (g p.base) (holonomy A p.boundary)

/-- Apply a continuous linear screening map to a general source field. -/
def screenedEndpointOfSource {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (Xi : LocalField d G E) (T : E →L[ℂ] (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) :=
  Xi.postcomp ⟨T, T.continuous⟩

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem screenedEndpointOfSource_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Xi : LocalField d G E) (T : E →L[ℂ] (Fin n → ℂ))
    (A : Configuration d G) :
    screenedEndpointOfSource Xi T A = T (Xi A) :=
  rfl

omit [IsTopologicalGroup G] in
/-- An equivariant screening map turns source covariance into the endpoint
covariance used by screened Wilson lines. -/
theorem screenedEndpointOfSource_covariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (rho : ContinuousUnitaryRepData G n) (act : G → E → E)
    (x : Site d) (Xi : LocalField d G E)
    (hXi : SourceCovariantAt act x Xi)
    (T : E →L[ℂ] (Fin n → ℂ))
    (hT : ∀ g v, T (act g v) = representationAction rho g (T v)) :
    GaugeCovariantAt rho x (screenedEndpointOfSource Xi T) := by
  intro g A
  rw [screenedEndpointOfSource_apply, screenedEndpointOfSource_apply,
    hXi g A, hT]

omit [Group G] [IsTopologicalGroup G] in
/-- A source witness not killed by the screening map proves that the endpoint
is not the zero cylindrical function. -/
theorem screenedEndpointOfSource_ne_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Xi : LocalField d G E) (T : E →L[ℂ] (Fin n → ℂ))
    (A : Configuration d G) (h : T (Xi A) ≠ 0) :
    screenedEndpointOfSource Xi T A ≠ 0 := by
  simpa using h

section TensorEndpoint

variable {m : ℕ}

/-- Apply an equivariant continuous multilinear screening form to the axial
matrices of finitely many based loops.  This realizes an arbitrary ordinary
adjoint tensor power without imposing a normed topology on the algebraic
`PiTensorProduct` carrier. -/
def axialTensorEndpoint
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) where
  toContinuousMap :=
    ⟨fun A => T (fun i => Lie.axialMatrix eta (holonomy A (q i))), by
      apply T.coe_continuous.comp
      apply continuous_pi
      intro i
      exact Lie.continuous_axialMatrix eta |>.comp (continuous_holonomy (q i))⟩
  support := basedLoopSupport q
  dependsOn_support := by
    intro A B hAB
    apply congrArg T
    funext i
    apply congrArg (Lie.axialMatrix eta)
    apply holonomy_eq_of_eqOn_edgeSupport
    intro e he
    apply hAB e
    change e ∈ basedLoopSupport q
    rw [basedLoopSupport, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩

@[simp]
theorem axialTensorEndpoint_apply
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (A : Configuration d G) :
    axialTensorEndpoint eta q T A =
      T (fun i => Lie.axialMatrix eta (holonomy A (q i))) :=
  rfl

/-- Equivariance of the multilinear screening form gives exactly the endpoint
covariance required by the screened observable. -/
theorem axialTensorEndpoint_covariant
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      representationAction rho h (T v)) :
    GaugeCovariantAt rho x (axialTensorEndpoint eta q T) := by
  intro g A
  rw [axialTensorEndpoint_apply, axialTensorEndpoint_apply]
  have hpoint : (fun i => Lie.axialMatrix eta
      (holonomy (gaugeTransform g A) (q i))) =
      fun i => (eta.ρ (g x) : Matrix (Fin N) (Fin N) ℂ) *
        Lie.axialMatrix eta (holonomy A (q i)) *
          (eta.ρ (g x)⁻¹ : Matrix (Fin N) (Fin N) ℂ) := by
    funext i
    rw [holonomy_loop_gaugeTransform]
    exact Lie.axialMatrix_conj eta (g x) (holonomy A (q i))
  rw [hpoint, hT]

/-- A prescribed loop-holonomy witness proves the constructed axial tensor
endpoint is nonzero. -/
theorem axialTensorEndpoint_ne_at
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (A : Configuration d G)
    (h : T (fun i => Lie.axialMatrix eta (holonomy A (q i))) ≠ 0) :
    axialTensorEndpoint eta q T A ≠ 0 := by
  simpa using h

/-- Independent loop holonomies and one axial tensor witness imply that the
constructed endpoint is a nonzero cylindrical function. -/
theorem axialTensorEndpoint_nonzero
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hq : BasedLoopHolonomySurjective (G := G) q)
    (hdetect : ∃ u : Fin m → G,
      T (fun i => Lie.axialMatrix eta (u i)) ≠ 0) :
    ∃ A : Configuration d G, axialTensorEndpoint eta q T A ≠ 0 := by
  obtain ⟨u, hu⟩ := hdetect
  obtain ⟨A, hA⟩ := hq u
  refine ⟨A, ?_⟩
  rw [axialTensorEndpoint_apply]
  simpa only [hA] using hu

end TensorEndpoint

end

end YangMills.Gluelump.Endpoint
