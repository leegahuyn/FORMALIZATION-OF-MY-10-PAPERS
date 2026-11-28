import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageComma

/-! The actual geometric affine étale indexing category can
be taken in the same universe as the chart's coordinate ring. -/

namespace ManuscriptAudit.NativeAffineEtaleStageSmall

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 2600000 in
/-- Actual affine stages have a small model in the ring universe,
using the actual affine étale site and genuine chart-to-stage arrows. -/
theorem essentiallySmall_stage : EssentiallySmall.{u} (Stage A B) := by
  let X := ProetaleAffineTensor.spectrum A
  let C := X.AffineEtaleᵒᵖ
  let L := (NativeAffineEtaleStageComma.affineInclusion (A := A)).op
  let T := op (ProetaleAffineTensor.object A B)
  let E : C ≌ SmallModel.{u} C := equivSmallModel.{u} C
  let P := CostructuredArrow.pre E.inverse L T
  let e : Stage A B ≌ CostructuredArrow (E.inverse ⋙ L) T :=
    (NativeAffineEtaleStageComma.equivalence (A := A) (B := B)).trans P.asEquivalence.symm
  exact EssentiallySmall.mk' e

end
end ManuscriptAudit.NativeAffineEtaleStageSmall

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleStageSmall.essentiallySmall_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
