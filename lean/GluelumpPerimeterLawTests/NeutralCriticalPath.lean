/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState
import GluelumpPerimeterLaw.Propagation.AxisTransport
import GluelumpPerimeterLaw.Propagation.CanonicalCofinalPerimeterLaw
import GluelumpPerimeterLaw.Propagation.CanonicalCofinalRectangle
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation
import GluelumpPerimeterLaw.Propagation.CanonicalRectanglePerimeter
import GluelumpPerimeterLaw.Propagation.CanonicalRectangleTransport
import GluelumpPerimeterLaw.Propagation.CofinalRectangleCertificate
import GluelumpPerimeterLaw.Propagation.PaperCorner
import GluelumpPerimeterLaw.Propagation.CouplingRate
import GluelumpPerimeterLaw.Propagation.ConjSpanCornerExpectation
import GluelumpPerimeterLaw.Propagation.ConjSpanPerimeterLaw
import GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightExpectation
import GluelumpPerimeterLaw.Propagation.CornerReflectionState
import GluelumpPerimeterLaw.Propagation.Perimeter
import GluelumpPerimeterLaw.Propagation.RectangleGeometryCore
import GluelumpPerimeterLaw.Propagation.RectangleReflectionCore
import ImportGraph.Graph.TransitiveClosure
import ImportGraph.Imports.ImportGraph
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Neutral gluelump critical-path regression

This focused test enforces two extraction invariants:

* each listed neutral module has no transitive import below
  `YangMills.StrongCoupling` or `YangMills.Polymer`;
* representative public theorems use only Lean's standard proof axioms
  `propext`, `Classical.choice`, and `Quot.sound`.

Add each new neutral headline module and theorem here as Tasks 4--6 land.
The separate completed-free-boundary-limit application is intentionally not a
root: it is a one-way adapter from `StrongCoupling` into this audited core.
-/

open Lean Meta Elab Command

private def neutralCriticalPathRoots : Array Name := #[
  `GluelumpPerimeterLaw.Upstream.Gauge.ReflectionPositiveState,
  `GluelumpPerimeterLaw.Propagation.AxisTransport,
  `GluelumpPerimeterLaw.Propagation.CanonicalCofinalPerimeterLaw,
  `GluelumpPerimeterLaw.Propagation.CanonicalCofinalRectangle,
  `GluelumpPerimeterLaw.Propagation.CanonicalRectangleExpectation,
  `GluelumpPerimeterLaw.Propagation.CanonicalRectanglePerimeter,
  `GluelumpPerimeterLaw.Propagation.CanonicalRectangleTransport,
  `GluelumpPerimeterLaw.Propagation.CofinalRectangleCertificate,
  `GluelumpPerimeterLaw.Propagation.PaperCorner,
  `GluelumpPerimeterLaw.Propagation.PaperCornerEndpoints,
  `GluelumpPerimeterLaw.Propagation.CouplingRate,
  `GluelumpPerimeterLaw.Propagation.ConjSpanCornerExpectation,
  `GluelumpPerimeterLaw.Propagation.ConjSpanPerimeterLaw,
  `GluelumpPerimeterLaw.Propagation.ConjSpanPhysicalStraightExpectation,
  `GluelumpPerimeterLaw.Propagation.CornerReflectionState,
  `GluelumpPerimeterLaw.Propagation.Perimeter,
  `GluelumpPerimeterLaw.Propagation.RectangleGeometryCore,
  `GluelumpPerimeterLaw.Propagation.RectangleReflectionCore
]

private def forbiddenNeutralImport (moduleName : Name) : Bool :=
  (`YangMills.StrongCoupling).isPrefixOf moduleName ||
    (`GluelumpPerimeterLaw.Upstream.StrongCoupling).isPrefixOf moduleName ||
    (`YangMills.Polymer).isPrefixOf moduleName

run_cmd do
  let env ← getEnv
  let closure := env.importGraph.transitiveClosure
  for root in neutralCriticalPathRoots do
    let imports ← match closure.find? root with
      | some imports => pure imports
      | none => throwError m!"neutral root {root} is absent from the import graph"
    for moduleName in imports do
      if forbiddenNeutralImport moduleName then
        throwError m!"neutral root {root} transitively imports forbidden module {moduleName}"

/-- Fail elaboration unless a declaration's complete axiom footprint is the
standard proposition-extensionality/choice/quotient set allowed by this
project. -/
elab "assert_only_standard_axioms " n:ident : command => do
  let name ← liftCoreM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed : NameSet := NameSet.ofList
    [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError m!"{name} depends on nonstandard axiom {axiomName}"

open YangMills.Gluelump.Propagation

assert_only_standard_axioms
  conjSpanPhysicalStraightExpectation_rate_power_le
assert_only_standard_axioms
  Gauge.ReflectionPositiveState.diagonalRowBending
assert_only_standard_axioms
  Gauge.ReflectionPositiveState.antiDiagonalMatrixClosing
assert_only_standard_axioms
  conjugateHolonomyMatrix_antiDiagonalFamilySelfProduct_apply
assert_only_standard_axioms
  conjugateHolonomyMatrix_rankOne_antiDiagonalFamilyProduct_apply
assert_only_standard_axioms
  CofinalRectangleReflectionCertificate.perimeter_lower_bound_of_line_rate
assert_only_standard_axioms
  AxisSwapInvariant.eq_of_distinct
assert_only_standard_axioms
  AxisSwapInvariant.im_eq_zero_of_distinct
assert_only_standard_axioms
  CanonicalRectangleExpectationCertificate.toCofinal
assert_only_standard_axioms
  exists_positive_rate_of_rectangle_perimeter_power
assert_only_standard_axioms
  perimeterLaw_of_cofinalRectangleCertificate_fixedRate
assert_only_standard_axioms
  perimeterLaw_of_cofinalRectangleCertificate
assert_only_standard_axioms
  conjSpanPhysicalStraightExpectation_sq_le_cornerBent_odd
assert_only_standard_axioms
  conjSpanCornerBent_sq_div_dimension_le_square_odd
assert_only_standard_axioms
  conjSpanCornerSquareExpectation_eq_canonicalRectangleExpectation_odd
assert_only_standard_axioms
  conjSpanCofinalRectangleReflectionCertificate
assert_only_standard_axioms
  conjSpanPerimeterLaw_of_positiveOneLink
assert_only_standard_axioms
  diagonalReflect_rectangleBoundary
assert_only_standard_axioms
  wilsonLoop_rectangleBoundary_diagonalReflectConfiguration_swap
assert_only_standard_axioms
  rectangleBoundary_swap_axes_eq_reverse
assert_only_standard_axioms
  canonicalRectangleIntegral_im_eq_zero
assert_only_standard_axioms
  canonicalRectangleExpectation_nonneg
assert_only_standard_axioms
  canonicalRectangleExpectation_le_one
assert_only_standard_axioms
  canonicalRectangleExpectation_width_reflectionLogConvex
assert_only_standard_axioms
  canonicalRectangleExpectation_transpose
assert_only_standard_axioms
  canonicalRectangleExpectationCertificate
assert_only_standard_axioms
  RectangleAxisSwapInvariant.axisSwapInvariant
assert_only_standard_axioms
  rectangleBoundaryIntegral_eq_of_distinct
assert_only_standard_axioms
  rectangleBoundaryIntegral_eq_integral_rectangleBoundary
assert_only_standard_axioms
  canonicalRectangleIntegral_eq_integral_rectangleBoundary
assert_only_standard_axioms
  integral_rectangleBoundary_eq_re_of_canonical
assert_only_standard_axioms
  rectangleBoundary_power_lower_bound_of_canonical
assert_only_standard_axioms
  rectangleBoundary_exp_lower_bound_of_canonical

assert_only_standard_axioms
  paperPhysicalStraightExpectation_sq_le_cornerBent
assert_only_standard_axioms
  paperCornerBent_sq_div_dimension_le_square
assert_only_standard_axioms
  paperRectangle_lower_bound_of_line_rate
assert_only_standard_axioms
  exp_neg_couplingWeight_rectangle_le_square
