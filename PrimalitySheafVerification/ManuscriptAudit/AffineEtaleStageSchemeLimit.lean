import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Opposites
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeColimit

/-! The actual affine scheme of the chart is the limit of the
literal affine schemes of its genuine affine étale stages. -/

namespace ManuscriptAudit.AffineEtaleStageSchemeLimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage ringDiagram chartCocone)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

/-- The actual contravariant Spec diagram has the given chart as its cone point. -/
abbrev schemeCone : Cone ((ringDiagram (A := A) (B := B)).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (chartCocone (A := A) (B := B)).op

/-- The actual Spec cone is a cofiltered scheme limit, with the
canonical affine chart itself as its point. -/
def isLimit_schemeCone (hApprox : FiniteTupleApproximation A B) :
    IsLimit (schemeCone (A := A) (B := B)) :=
  isLimitOfPreserves Scheme.Spec (AffineEtaleStageColimit.isColimit_chart hApprox).op

end
end ManuscriptAudit.AffineEtaleStageSchemeLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageSchemeLimit.isLimit_schemeCone
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
