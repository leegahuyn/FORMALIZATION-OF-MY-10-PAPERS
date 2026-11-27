import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeFibers

/-! The geometric fibre is the actual base change of the canonical arithmetic nodal fibre at the same odd prime. -/

namespace ManuscriptAudit.IntegralNodalGeometricFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralOddPrimeFibers (residueBase nodalFiber nodeToResidue)
open IntPrimeResidueFiber (closedPoint residueSpecIso residueSpecIso_over)
open PlaneEquationBaseChange (changeBase)
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

abbrev closureField := AlgebraicClosure (ZMod p)

private abbrev base := Spec (CommRingCat.of ℤ)
private abbrev residueToBase := base.fromSpecResidueField (closedPoint p)
private abbrev totalToBase := NodalIntegralGluing.toBase ℤ

/-- The geometric point over the actual prime ideal (p). -/
def geometricResidueMap : Spec (CommRingCat.of (closureField p)) ⟶ residueBase p :=
  changeBase (ZMod p) (closureField p) ≫ (residueSpecIso p).hom

/-- The geometric fibre is the genuine pullback of the canonical arithmetic fibre. -/
abbrev geometricFiber := pullback (geometricResidueMap p) (nodeToResidue p)

def geometricToBase : geometricFiber p ⟶ Spec (CommRingCat.of (closureField p)) :=
  pullback.fst _ _

instance geometric_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (geometricToBase p) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (geometricResidueMap p) (nodeToResidue p)))

private theorem geometricResidueMap_over :
    geometricResidueMap p ≫ residueToBase p = changeBase ℤ (closureField p) := by
  rw [geometricResidueMap, Category.assoc, residueSpecIso_over]
  change Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (closureField p))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq ℤ (ZMod p) (closureField p)).symm

private def toIntegralFiber :
    geometricFiber p ≅ IntegralNodalArithmeticBump.fiber (closureField p) :=
  pullbackRightPullbackFstIso (residueToBase p) totalToBase (geometricResidueMap p) ≪≫
    pullback.congrHom (geometricResidueMap_over p) rfl

private theorem toIntegralFiber_over :
    (toIntegralFiber p).hom ≫ IntegralNodalArithmeticBump.fiberToBase (closureField p) =
      geometricToBase p := by
  change ((pullbackRightPullbackFstIso (residueToBase p) totalToBase (geometricResidueMap p)).hom ≫
    (pullback.congrHom (geometricResidueMap_over p) (rfl : totalToBase = totalToBase)).hom) ≫
      pullback.fst (changeBase ℤ (closureField p)) totalToBase =
    pullback.fst (geometricResidueMap p) (nodeToResidue p)
  rw [Category.assoc]
  have h := pullbackRightPullbackFstIso_hom_fst (residueToBase p) totalToBase (geometricResidueMap p)
  simpa only [pullback.congrHom, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id] using h

/-- The canonical geometric fibre is the actual proper node over the algebraic closure. -/
def projectiveIso : geometricFiber p ≅ projectiveNode (closureField p) :=
  toIntegralFiber p ≪≫ IntegralNodalArithmeticBump.fiberIso (closureField p)

theorem projectiveIso_over :
    (projectiveIso p).hom ≫ projectiveNodeToBase (closureField p) = geometricToBase p := by
  change ((toIntegralFiber p).hom ≫
    (IntegralNodalArithmeticBump.fiberIso (closureField p)).hom) ≫ _ = _
  rw [Category.assoc, IntegralNodalArithmeticBump.fiberIso_over, toIntegralFiber_over]

theorem geometric_proper : IsProper (geometricToBase p) := by
  letI := NodalProjectiveClosure.projectiveNode_isProper (closureField p)
  rw [← projectiveIso_over]
  infer_instance

end
end ManuscriptAudit.IntegralNodalGeometricFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalGeometricFiber.projectiveIso,
      ``ManuscriptAudit.IntegralNodalGeometricFiber.projectiveIso_over,
      ``ManuscriptAudit.IntegralNodalGeometricFiber.geometric_proper] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
