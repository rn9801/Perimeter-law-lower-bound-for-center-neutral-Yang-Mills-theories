/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.Construction
import GluelumpPerimeterLaw.Endpoint.ReflectionSupport
import GluelumpPerimeterLaw.Endpoint.TransverseLoops

/-!
# Concrete normalized endpoints in three lattice directions

This specializes the general axial tensor endpoint to the explicit nested
transverse loops.  Independent holonomy prescription is now a theorem, so a
single axial detection tuple suffices for endpoint nonvanishing.
-/

namespace YangMills.Gluelump.Endpoint

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson
open scoped Matrix

noncomputable section

variable {d m n N : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- The concrete normalized axial endpoint based on nested loops in the
coordinate plane spanned by axes `1` and `2`. -/
def transverseAxialEndpoint
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
  (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    LocalField d G (Fin n → ℂ) :=
  normalizedAxialTensorEndpoint eta (transverseLoop (m := m) hd x) T

@[simp]
theorem transverseAxialEndpoint_support
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    (transverseAxialEndpoint hd eta x T).support =
      basedLoopSupport (transverseLoop (m := m) hd x) :=
  rfl

/-- An equivariant screening form makes the concrete transverse endpoint
dual-covariant at its base site. -/
theorem transverseAxialEndpoint_covariant
    (hd : 3 ≤ d) (rho : ContinuousUnitaryRepData G n)
    (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hT : ∀ h v,
      T (fun i => (eta.ρ h : Matrix (Fin N) (Fin N) ℂ) * v i *
        (eta.ρ h⁻¹ : Matrix (Fin N) (Fin N) ℂ)) =
      dualAction rho h (T v)) :
    GaugeCovariantAt rho x (transverseAxialEndpoint hd eta x T) :=
  normalizedAxialTensorEndpoint_covariant rho eta
    (transverseLoop (m := m) hd x) T hT

/-- The concrete transverse endpoint is pointwise normalized. -/
theorem transverseAxialEndpoint_l2Norm_le_one
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (A : Configuration d G) :
    endpointL2Norm (transverseAxialEndpoint hd eta x T A) ≤ 1 :=
  normalizedAxialTensorEndpoint_l2Norm_le_one eta
    (transverseLoop (m := m) hd x) T A

/-- The transverse endpoint collar lies in the coordinate-site positive half
whose boundary passes through its base. -/
theorem transverseAxialEndpoint_supportedInSitePositiveHalf
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    (transverseAxialEndpoint hd eta x T).SupportedInSitePositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd)) := by
  intro e he
  rw [transverseAxialEndpoint_support] at he
  have hplane := basedLoopSupport_transverseLoop_armPlane hd x e he
  omega

/-- The same collar belongs to the adjacent link-positive half-lattice. -/
theorem transverseAxialEndpoint_supportedInLinkPositiveHalf
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ)) :
    (transverseAxialEndpoint hd eta x T).SupportedInLinkPositiveHalf
      (Geometry.armAxis hd) (x (Geometry.armAxis hd) - 1) := by
  intro e he
  rw [transverseAxialEndpoint_support] at he
  have hplane := basedLoopSupport_transverseLoop_armPlane hd x e he
  omega

/-- A single axial detection tuple proves the explicit transverse endpoint is
not the zero cylindrical field. -/
theorem transverseAxialEndpoint_nonzero
    (hd : 3 ≤ d) (eta : ContinuousUnitaryRepData G N) (x : Site d)
    (T : ContinuousMultilinearMap ℂ
      (fun _ : Fin m => Matrix (Fin N) (Fin N) ℂ) (Fin n → ℂ))
    (hdetect : ∃ u : Fin m → G,
      T (fun i => Lie.axialMatrix eta (u i)) ≠ 0) :
    ∃ A : Configuration d G, transverseAxialEndpoint hd eta x T A ≠ 0 :=
  normalizedAxialTensorEndpoint_nonzero eta
    (transverseLoop (m := m) hd x) T
    (transverseLoop_holonomySurjective (m := m) hd x) hdetect

end

end YangMills.Gluelump.Endpoint
