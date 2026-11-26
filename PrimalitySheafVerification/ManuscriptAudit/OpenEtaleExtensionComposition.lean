import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# Nested opens and constant étale sheaves

Restriction along an open immersion is the usual inverse image on the
small étale site. Composition of the corresponding left adjoints gives
the canonical extension map from the smaller open to the larger open.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SmallEtaleBaseChange

noncomputable section

universe u

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]

private abbrev C := AddCommGrpCat.{u}

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Restriction along an open immersion is left adjoint to its usual direct image. -/
def restrictionDirectImageAdjunction : restriction j C.{u} ⊣ directImage j C := by
  letI := postcomposeContinuous j
  letI := isContinuous_of_baseChange j
  let a : etalePostcompose j ⊣ etaleBaseChange j :=
    MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ j
      (show Etale j from inferInstance) trivial
  exact a.sheafPushforwardContinuous (E := C.{u}) U.smallEtaleTopology X.smallEtaleTopology

/-- Restricting the constant abelian-group sheaf gives the constant sheaf on the open. -/
def restrictionConstantIso : constantSheaf X.smallEtaleTopology C.{u} ⋙ restriction j C.{u} ≅
    constantSheaf U.smallEtaleTopology C := by
  letI := SmallEtaleBaseChange.preservesFiniteLimits j
  let aX := constantSheafAdj X.smallEtaleTopology C.{u} (terminalIsTerminal (C := X.Etale))
  let aU := constantSheafAdj U.smallEtaleTopology C.{u}
    (isLimitOfHasTerminalOfPreservesLimit (etaleBaseChange j))
  exact (aX.comp (restrictionDirectImageAdjunction j)).leftAdjointUniq aU

/-- Restriction along nested opens is restriction along their composite. -/
def restrictionCompIso : restriction j C.{u} ⋙ restriction i C.{u} ≅ restriction (i ≫ j) C := by
  letI := postcomposeContinuous i
  letI := postcomposeContinuous j
  letI := postcomposeContinuous (i ≫ j)
  let e : etalePostcompose (i ≫ j) ≅ etalePostcompose i ⋙ etalePostcompose j :=
    MorphismProperty.Over.mapComp (P := @AlgebraicGeometry.Etale) ⊤
      (show Etale i from inferInstance) (show Etale j from inferInstance)
  exact Functor.sheafPushforwardContinuousComp' (eFG := e.symm) (A := C.{u})
    (J := V.smallEtaleTopology) (K := U.smallEtaleTopology) (L := X.smallEtaleTopology)

/-- Extension by zero along nested opens is extension along their composite. -/
def extensionByZeroCompIso : extensionByZero i C.{u} ⋙ extensionByZero j C.{u} ≅
    extensionByZero (i ≫ j) C :=
  (((abelianExtensionByZeroAdjunction i).comp (abelianExtensionByZeroAdjunction j))
    .ofNatIsoRight (restrictionCompIso i j)).leftAdjointUniq
      (abelianExtensionByZeroAdjunction (i ≫ j))

/-- The canonical map from the constant sheaf extended by zero from the smaller
open to the constant sheaf extended by zero from the larger open. -/
def nestedOpenConstantMap (M : C.{u}) :
    (extensionByZero (i ≫ j) C.{u}).obj ((constantSheaf V.smallEtaleTopology C.{u}).obj M) ⟶
    (extensionByZero j C.{u}).obj ((constantSheaf U.smallEtaleTopology C.{u}).obj M) :=
  (extensionByZeroCompIso i j).inv.app _ ≫
    (extensionByZero j C.{u}).map
      (((abelianExtensionByZeroAdjunction i).homEquiv _ _).symm
        ((restrictionConstantIso i).inv.app M))

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.restrictionDirectImageAdjunction,
      ``ManuscriptAudit.OpenEtaleExtension.restrictionConstantIso,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZeroCompIso,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenConstantMap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
