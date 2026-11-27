import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralModelBaseChange
import PrimalitySheafVerification.ManuscriptAudit.NodalGluedFieldModel
import PrimalitySheafVerification.ManuscriptAudit.NodalArithmeticBump
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusUnderIso

/-! The arithmetic zero-bump counterexample on the actual special fiber
of the flat integral nodal model. -/

namespace ManuscriptAudit.IntegralNodalArithmeticBump

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing (model toBase)
open PlaneEquationBaseChange (changeBase)
open NodalGluedFieldModel (modelIso modelIso_over)
open NodalIntegralModelBaseChange (model_square_isPullback)
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 7000
set_option maxHeartbeats 700000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

/-- The actual field pullback of the integral nodal scheme. -/
abbrev fiber := pullback (changeBase ℤ K) (toBase ℤ)

def fiberToBase : fiber K ⟶ Spec (CommRingCat.of K) := pullback.fst _ _

instance fiber_locallyOfFinitePresentation : LocallyOfFinitePresentation (fiberToBase K) := by
  letI : LocallyOfFinitePresentation (toBase ℤ) :=
    NodalIntegralGluing.model_locallyOfFinitePresentation ℤ
  exact inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (changeBase ℤ K) (toBase ℤ)))

/-- The whole field fiber, including its point at infinity, is the
proper projective node constructed independently. -/
def fiberIso : fiber K ≅ projectiveNode K :=
  (model_square_isPullback ℤ K).isoPullback.symm ≪≫ modelIso K

theorem fiberIso_over : (fiberIso K).hom ≫ projectiveNodeToBase K = fiberToBase K := by
  change ((model_square_isPullback ℤ K).isoPullback.inv ≫ (modelIso K).hom) ≫
    projectiveNodeToBase K = _
  rw [Category.assoc, modelIso_over]
  exact (model_square_isPullback ℤ K).isoPullback_inv_fst

theorem fiber_proper : IsProper (fiberToBase K) := by
  letI : IsProper (projectiveNodeToBase K) := NodalProjectiveClosure.projectiveNode_isProper K
  rw [← fiberIso_over]
  infer_instance

theorem fiber_not_smooth : ¬ AlgebraicGeometry.Smooth (fiberToBase K) := by
  intro h
  letI : AlgebraicGeometry.Smooth (fiberToBase K) := h
  have hi : (fiberIso K).inv ≫ fiberToBase K = projectiveNodeToBase K := by
    rw [← fiberIso_over, Iso.inv_hom_id_assoc]
  have hs : AlgebraicGeometry.Smooth ((fiberIso K).inv ≫ fiberToBase K) := inferInstance
  exact NodalSmoothCharts.projectiveNode_not_smooth K (hi ▸ hs)

def smoothFiberIso :
    (fiberToBase K).smoothLocus.toScheme ≅ NodalSmoothLocusOverlap.smoothScheme K :=
  SmoothLocusUnderIso.iso (fiberIso K) (fiberToBase K)
    (projectiveNodeToBase K) (fiberIso_over K)

private abbrev F₅ := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev M := ZMod 2
private abbrev C := AddCommGrpCat.{0}
private abbrev coeff := AddCommGrpCat.of M

private abbrev X := fiber F₅
private abbrev U := (fiberToBase F₅).smoothLocus.toScheme

abbrev fiberHOne := Sheaf.H ((constantSheaf X.smallEtaleTopology C).obj coeff) 1
abbrev smoothHOne := Sheaf.H ((constantSheaf U.smallEtaleTopology C).obj coeff) 1

def fiberModule : Module M fiberHOne :=
  BinaryConstantCohomology.coefficientModule X.smallEtaleTopology 1

def smoothModule : Module M smoothHOne :=
  BinaryConstantCohomology.coefficientModule U.smallEtaleTopology 1

/-- The actual arithmetic fiber at five has zero signed bump and is nonsmooth. -/
theorem f5_zero_bump_and_not_smooth :
    letI := fiberModule
    letI := smoothModule
    ((Module.finrank M fiberHOne : ℤ) - Module.finrank M smoothHOne = 0) ∧
      ¬ AlgebraicGeometry.Smooth (fiberToBase F₅) := by
  letI := fiberModule
  letI := smoothModule
  letI := NodalArithmeticBump.properModule F₅
  letI := NodalArithmeticBump.smoothModule F₅
  let e := schemeIsoCohomologyEquiv (fiberIso F₅) coeff 1
  let f := schemeIsoCohomologyEquiv (smoothFiberIso F₅) coeff 1
  let eL : fiberHOne ≃ₗ[M] NodalArithmeticProjectiveHOne.properHOne F₅ :=
    { e with map_smul' := ZMod.map_smul e }
  let fL : smoothHOne ≃ₗ[M] NodalArithmeticBump.smoothHOne F₅ :=
    { f with map_smul' := ZMod.map_smul f }
  refine ⟨?_, fiber_not_smooth F₅⟩
  rw [eL.finrank_eq, fL.finrank_eq]
  exact NodalArithmeticBump.f5_zero_bump_and_not_smooth.1

end
end ManuscriptAudit.IntegralNodalArithmeticBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalArithmeticBump.fiberIso,
      ``ManuscriptAudit.IntegralNodalArithmeticBump.fiberIso_over,
      ``ManuscriptAudit.IntegralNodalArithmeticBump.fiber_proper,
      ``ManuscriptAudit.IntegralNodalArithmeticBump.smoothFiberIso,
      ``ManuscriptAudit.IntegralNodalArithmeticBump.f5_zero_bump_and_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
