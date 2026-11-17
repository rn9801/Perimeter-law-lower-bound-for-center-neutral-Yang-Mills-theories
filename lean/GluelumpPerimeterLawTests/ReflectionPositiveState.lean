/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.StrongCoupling.FreeBoundaryReflectionPositiveState

/-!
# Regression checks for the neutral reflection-positive-state interface
-/

#check YangMills.Gauge.ReflectionPositiveState
#check YangMills.Gauge.ReflectionPositiveState.siteFamilyPositive
#check YangMills.Gauge.ReflectionPositiveState.siteFamilyCauchySchwarz
#check YangMills.Gauge.ReflectionPositiveState.diagonalFamilyCauchySchwarz
#check YangMills.Gauge.ReflectionPositiveState.antiDiagonalFamilyCauchySchwarz

namespace YangMills.StrongCoupling

#check IsTranslationInvariantFreeBoundaryLimit.reflectionPositiveState
#check IsTranslationInvariantFreeBoundaryLimit.linkCrossingFamilyPositive
#check IsTranslationInvariantFreeBoundaryLimit.linkCrossingFamilyCauchySchwarz

#print axioms IsTranslationInvariantFreeBoundaryLimit.reflectionPositiveState
#print axioms IsTranslationInvariantFreeBoundaryLimit.linkCrossingFamilyPositive

end YangMills.StrongCoupling

#print axioms YangMills.Gauge.ReflectionPositiveState.siteFamilyCauchySchwarz
#print axioms YangMills.Gauge.ReflectionPositiveState.diagonalFamilyCauchySchwarz
