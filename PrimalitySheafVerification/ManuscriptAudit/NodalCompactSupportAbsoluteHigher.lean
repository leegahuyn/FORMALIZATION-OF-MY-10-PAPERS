import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHigherFromCharts

/-! Absolute all-degree higher vanishing for the genuine split nodal curve. -/

namespace ManuscriptAudit.NodalCompactSupportAbsoluteHigher

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalCompactSupportHOne (nodalHc)

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

/-- The native proper nodal cohomology vanishes in every degree at least three. -/
theorem projective_H_add_three_subsingleton (h2 : (2 : K) ≠ 0) (d : ℕ)
    [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) (n + 3)) :=
  NodalCompactSupportHigherFromCharts.projective_H_add_three_subsingleton K d n
    (NodalAffineHigherCohomology.affine_H_add_two_subsingleton K h2 d (n + 1))

/-- The actual compact-support groups of the affine nodal curve vanish in every degree at least three. -/
theorem compact_H_add_three_subsingleton (h2 : (2 : K) ≠ 0) (d : ℕ)
    [NeZero (d : K)] (n : ℕ) :
    Subsingleton (nodalHc K (AddCommGrpCat.of (ZMod d)) (n + 3)) :=
  NodalCompactSupportHigherFromCharts.compact_H_add_three_subsingleton K d n
    (NodalAffineHigherCohomology.affine_H_add_two_subsingleton K h2 d (n + 1))

end ManuscriptAudit.NodalCompactSupportAbsoluteHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportAbsoluteHigher.projective_H_add_three_subsingleton,
      ``ManuscriptAudit.NodalCompactSupportAbsoluteHigher.compact_H_add_three_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
