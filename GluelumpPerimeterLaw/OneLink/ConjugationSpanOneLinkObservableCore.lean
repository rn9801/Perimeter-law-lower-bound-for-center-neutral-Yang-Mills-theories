/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Endpoint.ConjugationSpanScreenedWilsonLine
import GluelumpPerimeterLaw.OneLink.ReflectedEndpointObservableCore

/-!
# The direct conjugation-span one-link observable

This neutral module defines the local one-link seed.  Its completed-box Gram
factorization and strict lower bound remain in downstream adapter modules.
-/

namespace YangMills.Gluelump.OneLink

open Gauge Lattice.Cubic Wilson Endpoint Propagation
open RepresentationTheory Representation

noncomputable section

universe u

variable {d m n r : ℕ} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The reflected one-bond seed made from the direct conjugation-span
endpoint on the positive side of the distinguished arm bond. -/
def conjSpanReflectedOneLinkObservable
    (hd : 3 ≤ d) (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho).dual)
    (z : Site d) (hz : z (Geometry.armAxis hd) = 0) :
    LocalObservable d G :=
  reflectedEndpointOneLinkObservable rho
    (conjSpanPhi hd sigma rho T
      (step z (.forward (Geometry.armAxis hd))))
    (Geometry.armAxis hd) z hz

end

end YangMills.Gluelump.OneLink
