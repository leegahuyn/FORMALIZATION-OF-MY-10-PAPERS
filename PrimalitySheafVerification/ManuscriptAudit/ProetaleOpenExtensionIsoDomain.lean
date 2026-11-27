import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionComposition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleSheaves

/-! Actual pro-étale extension by zero of constant coefficients depends on
the open immersion up to genuine isomorphism of its source. -/

namespace ManuscriptAudit.ProetaleOpenExtensionIsoDomain

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension
open SchemeIsoProetaleSheaves (sheafEquivalence)
open ProetaleOpenExtensionComposition (extensionByZeroCompIso)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleConstantRestriction (constant)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

variable {V U X : Scheme.{0}} (e : V ≅ U) (j : U ⟶ X) [IsOpenImmersion j]

/-- Along an actual scheme isomorphism, extension by zero is ordinary sheaf transport. -/
def extensionEquivalenceIso :
    extensionByZero e.hom A ≅ (sheafEquivalence e).functor := by
  let a : extensionByZero e.hom A ⊣ (sheafEquivalence e).inverse :=
    abelianExtensionByZeroAdjunction e.hom
  exact a.leftAdjointUniq (sheafEquivalence e).toAdjunction

/-- Transporting the source of the compactifying open transports its native constant extension. -/
def extensionConstantIsoOfSourceIso (M : Type) [AddCommGroup M] :
    (extensionByZero (e.hom ≫ j) A).obj (constant V M) ≅
      (extensionByZero j A).obj (constant U M) := by
  let c := AddCommGrpCat.of (ULift.{1} M)
  let h : (sheafEquivalence e).functor.obj (constant V M) ≅ constant U M :=
    (restrictionConstantIso.{0} e.inv).app c
  exact ((extensionByZeroCompIso e.hom j).symm.app (constant V M)) ≪≫
    (extensionByZero j A).mapIso (((extensionEquivalenceIso e).app (constant V M)) ≪≫ h)

/-- Equal arrows with their open-immersion structures have the same native extension. -/
def extensionCongr {Y X : Scheme.{0}} (j k : Y ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    extensionByZero j A ≅ extensionByZero k A := by
  subst k
  exact Iso.refl _

end
end ManuscriptAudit.ProetaleOpenExtensionIsoDomain

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenExtensionIsoDomain.extensionEquivalenceIso,
      ``ManuscriptAudit.ProetaleOpenExtensionIsoDomain.extensionConstantIsoOfSourceIso,
      ``ManuscriptAudit.ProetaleOpenExtensionIsoDomain.extensionCongr] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
