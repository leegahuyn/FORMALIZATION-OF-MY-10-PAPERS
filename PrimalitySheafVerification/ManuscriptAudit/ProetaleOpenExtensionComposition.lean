import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension

/-! Restrictions and extensions by zero for nested actual pro-étale opens. -/

namespace ManuscriptAudit.ProetaleOpenExtensionComposition

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u + 1}

/-- Restricting through two native pro-étale opens is restriction through their composite. -/
def restrictionCompIso :
    restriction j A.{u} ⋙ restriction i A.{u} ≅ restriction (i ≫ j) A.{u} := by
  letI := postcomposeContinuous i
  letI := postcomposeContinuous j
  letI := postcomposeContinuous (i ≫ j)
  let e : proetalePostcompose (i ≫ j) ≅ proetalePostcompose i ⋙ proetalePostcompose j :=
    MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤
      (show WeaklyEtale i from inferInstance) (show WeaklyEtale j from inferInstance)
  exact Functor.sheafPushforwardContinuousComp' (eFG := e.symm) (A := A.{u})
    (J := Scheme.ProEt.topology V) (K := Scheme.ProEt.topology U) (L := Scheme.ProEt.topology X)

/-- Two actual native extensions by zero compose to extension through the composite open. -/
def extensionByZeroCompIso :
    extensionByZero i A.{u} ⋙ extensionByZero j A.{u} ≅ extensionByZero (i ≫ j) A.{u} := by
  let a := (abelianExtensionByZeroAdjunction i).comp (abelianExtensionByZeroAdjunction j)
  exact (a.ofNatIsoRight (restrictionCompIso i j)).leftAdjointUniq
    (abelianExtensionByZeroAdjunction (i ≫ j))

end
end ManuscriptAudit.ProetaleOpenExtensionComposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenExtensionComposition.restrictionCompIso,
      ``ManuscriptAudit.ProetaleOpenExtensionComposition.extensionByZeroCompIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
