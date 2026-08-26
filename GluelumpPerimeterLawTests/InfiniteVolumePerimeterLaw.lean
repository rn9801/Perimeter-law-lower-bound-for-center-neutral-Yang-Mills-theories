/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.InfiniteVolumePerimeterLaw
import GluelumpPerimeterLaw.Propagation.ConjSpanPerimeterLaw

/-!
# Regression checks for the center-neutral infinite-volume perimeter law

These checks pin both the model-neutral direct-field assembly theorem and its
completed-free-boundary strong-coupling application.
-/

#check YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
#check YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw

#print axioms YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
#print axioms YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
