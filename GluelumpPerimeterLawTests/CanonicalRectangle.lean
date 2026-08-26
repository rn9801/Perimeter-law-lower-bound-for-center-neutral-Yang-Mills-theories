/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectationLimit

/-!
# Regression checks for canonical Wilson-rectangle expectations

These checks pin the neutral reflection-positive certificate and its thin
completed-free-boundary-limit adapter.  In particular, the adapter exposes
half-integer link reflection, coordinate swaps, arbitrary basepoints, and
literal reality without changing the neutral theorem's dependencies.
-/

namespace YangMills.Gluelump.Propagation

#check CanonicalRectangleExpectationCertificate
#check canonicalRectangleExpectationCertificate

#print axioms canonicalRectangleExpectationCertificate

end YangMills.Gluelump.Propagation

namespace YangMills.StrongCoupling.IsTranslationInvariantFreeBoundaryLimit

#check canonicalRectangleLinkReflectionData
#check rectangleAxisSwapInvariant
#check canonicalRectangleExpectationCertificate
#check rectangleBoundaryExpectation_basepoint_eq_origin
#check rectangleBoundaryExpectation_im_eq_zero
#check rectangleBoundaryExpectation_axisSwap

#print axioms canonicalRectangleLinkReflectionData
#print axioms rectangleAxisSwapInvariant
#print axioms canonicalRectangleExpectationCertificate
#print axioms rectangleBoundaryExpectation_basepoint_eq_origin
#print axioms rectangleBoundaryExpectation_im_eq_zero
#print axioms rectangleBoundaryExpectation_axisSwap

end YangMills.StrongCoupling.IsTranslationInvariantFreeBoundaryLimit
