import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProperNormalizationFibers
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorEpi

/-! The actual proper nodal normalization sequence for discrete
abelian coefficients on the native pro-étale site. -/

namespace ManuscriptAudit.NodalProetaleConductorSequence

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap normalizationMap_integral)
open NodalNormalizedMapSurjectivity (properNormalization_surjective)
open NodalProetaleConductorBinary (plus minus plus_over minus_over)
open NodalSmoothRationalBoundary (projectiveOrigin)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The actual sequence consists of pro-étale functions, their
normalization direct image, and the rational origin direct image. -/
abbrev sequence :=
  ProetaleTwoBranchKernel.sequence (normalizationMap K) (projectiveOrigin K)
    (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2) M

variable [DiscreteTopology M]

/-- The diagonal and ordered branch difference form a short exact
sequence of actual pro-étale sheaves for every discrete abelian group. -/
theorem sequence_shortExact : (sequence K h2 M).ShortExact := by
  letI := normalizationMap_integral K
  letI := properNormalization_surjective K h2
  letI := NodalProetaleConductorEpi.difference_epi K h2 M
  exact ProetaleTwoBranchKernel.sequence_shortExact _ _ _ _ _ _ M
    (NodalProperNormalizationFibers.branchFibers K h2)

end
end ManuscriptAudit.NodalProetaleConductorSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProetaleConductorSequence.sequence_shortExact
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
