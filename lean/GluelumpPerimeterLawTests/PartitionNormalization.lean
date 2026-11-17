/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.OneLink.ConcretePartitionFunction

/-!
# Axiom regression for exact gluelump partition normalization

This narrow audit is intentionally independent of the unfinished propagation
modules.  It guards the exact boundary-coordinate permutation and the
constant-observable identification of the physical partition function.
-/

namespace YangMills.Tests.GluelumpPartitionNormalization

open Gluelump

#print axioms OneLink.measurePreserving_boundaryPairReorder
#print axioms OneLink.gaugeFixedPartitionPairing_eq_reorderedSplitPartition_of_real
#print axioms OneLink.re_gaugeFixedPartitionPairing_eq_reorderedSplitPartition
#print axioms OneLink.im_gaugeFixedPartitionPairing_eq_zero
#print axioms OneLink.partitionFunction_eq_linkGaugeFixedPairing
#print axioms OneLink.partitionFunction_eq_reorderedSplitPartition

end YangMills.Tests.GluelumpPartitionNormalization
