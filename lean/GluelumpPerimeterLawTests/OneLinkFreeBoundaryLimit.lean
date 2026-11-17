/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.FreeBoundaryLimitLowerBound

/-! Axiom regression for the direct one-link free-boundary limit bridge. -/

open YangMills.Gluelump.OneLink

#print axioms
  eventually_conjSpanOneLinkAdmissible_freeBoundarySpecification
#print axioms ConjSpanOneLinkAdmissible.gibbsExpectation_im_eq_zero
#print axioms
  centerNeutral_exists_uniform_conjSpanOneLink_freeBoundaryLimit_lowerBound
#print axioms
  centerNeutral_exists_uniform_translatedConjSpanOneLink_freeBoundaryLimit_lowerBound
