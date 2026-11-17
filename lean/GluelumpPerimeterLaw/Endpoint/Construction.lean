/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.AxialField
import GluelumpPerimeterLaw.Endpoint.Normalization

/-!
# Normalized axial tensor endpoints

This file packages the general matrix axial construction into the normalized
local endpoint consumed by screened Wilson observables.  The representation-
theoretic input is an equivariant continuous multilinear form; the geometric
input is independent prescription of the chosen based-loop holonomies.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open scoped Matrix

noncomputable section

variable {d m n N : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- The canonically normalized endpoint formed from axial matrices of a finite
family of based loops. -/
def normalizedAxialTensorEndpoint
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) :=
  normalizedEndpoint (axialTensorEndpoint eta q T)

@[simp]
theorem normalizedAxialTensorEndpoint_apply
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (A : Configuration d G) :
    normalizedAxialTensorEndpoint eta q T A =
      (endpointNormalizationScale (axialTensorEndpoint eta q T) : ℂ) •
        T (fun i => Lie.axialMatrix eta (holonomy A (q i))) := by
  rw [normalizedAxialTensorEndpoint, normalizedEndpoint_apply,
    axialTensorEndpoint_apply]

@[simp]
theorem normalizedAxialTensorEndpoint_support
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    (normalizedAxialTensorEndpoint eta q T).support = basedLoopSupport q := by
  rfl

/-- Equivariance of the screening form is preserved by canonical endpoint
normalization. -/
theorem normalizedAxialTensorEndpoint_covariant
    (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      representationAction rho h (T v)) :
    GaugeCovariantAt rho x (normalizedAxialTensorEndpoint eta q T) :=
  (axialTensorEndpoint_covariant rho eta q T hT).normalizedEndpoint rho x

/-- The normalized axial tensor endpoint has pointwise Euclidean norm at most
one, with no extra analytic hypothesis. -/
theorem normalizedAxialTensorEndpoint_l2Norm_le_one
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (A : Configuration d G) :
    endpointL2Norm (normalizedAxialTensorEndpoint eta q T A) ≤ 1 :=
  normalizedEndpoint_l2Norm_le_one (axialTensorEndpoint eta q T) A

/-- Independent loop holonomies and one axial detection tuple give a nonzero
normalized endpoint. -/
theorem normalizedAxialTensorEndpoint_nonzero
    (eta : ContinuousUnitaryRepData G N) {x : Site d}
    (q : Fin m → Lattice.Cubic.Path x x)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hq : BasedLoopHolonomySurjective (G := G) q)
    (hdetect : ∃ u : Fin m → G,
      T (fun i => Lie.axialMatrix eta (u i)) ≠ 0) :
    ∃ A : Configuration d G,
      normalizedAxialTensorEndpoint eta q T A ≠ 0 := by
  obtain ⟨A, hA⟩ := axialTensorEndpoint_nonzero eta q T hq hdetect
  exact ⟨A, normalizedEndpoint_ne_at _ A hA⟩

end

end YangMills.Gluelump.Endpoint
