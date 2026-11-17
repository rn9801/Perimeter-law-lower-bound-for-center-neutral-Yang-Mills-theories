/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.StraightGeometryCore

/-!
# The neutral reflected one-link endpoint observable

This file contains only the local observable used as the one-bond gluelump
seed.  Gauge-fixed finite-volume factorizations and positivity estimates live
in the downstream one-link adapter modules.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson Endpoint Propagation

noncomputable section

universe u

variable {d n : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The one-bond screened norm associated to a positive-side endpoint `Psi`.
The left endpoint is its literal bond-reflected pullback. -/
def reflectedEndpointOneLinkObservable
    (rho : ContinuousUnitaryRepData G n)
    (Psi : LocalField d G (Fin n → ℂ)) (tau : Fin d)
    (z : Site d) (hz : z tau = 0) : LocalObservable d G :=
  screenedObservable rho (Psi.linkPullback tau 0) Psi
    (reflectedFullPath tau 0 z hz (straightPositiveHalfPath tau z 0))

end

end YangMills.Gluelump.OneLink
