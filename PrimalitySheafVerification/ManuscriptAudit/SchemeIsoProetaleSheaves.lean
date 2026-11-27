import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! Authentic scheme isomorphisms give equivalences of native
pro-étale sheaves, preserving constants and continuous coefficients. -/

namespace ManuscriptAudit.SchemeIsoProetaleSheaves

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension (proetalePostcompose postcomposeContinuous restriction)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleContinuousDirectImageMaps (functions)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (e : X ≅ Y)

private abbrev J (T : Scheme.{0}) := Scheme.ProEt.topology T
private abbrev A := AddCommGrpCat.{1}

def siteEquivalence : X.ProEt ≌ Y.ProEt := by
  let F := proetalePostcompose e.hom
  let G := proetalePostcompose e.inv
  let hf : WeaklyEtale e.hom := inferInstance
  let hg : WeaklyEtale e.inv := inferInstance
  let unit : 𝟭 X.ProEt ≅ F ⋙ G :=
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X _ e.hom_inv_id).symm ≪≫
      MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤ hf hg
  let counit : G ⋙ F ≅ 𝟭 Y.ProEt :=
    (MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤ hg hf).symm ≪≫
      MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y _ e.inv_hom_id
  exact CategoryTheory.Equivalence.mk F G unit counit

/-- Restriction along the inverse isomorphism gives the actual equivalence of sheaves. -/
def sheafEquivalence : Sheaf (J X) A ≌ Sheaf (J Y) A := by
  let E := siteEquivalence e
  letI : E.functor.IsContinuous (J X) (J Y) := postcomposeContinuous e.hom
  letI : E.inverse.IsContinuous (J Y) (J X) := postcomposeContinuous e.inv
  let F := restriction e.inv A
  let G := restriction e.hom A
  let u : 𝟭 (Sheaf (J X) A) ≅ F ⋙ G :=
    (Functor.sheafPushforwardContinuousComp' (eFG := E.unitIso.symm) (A := A)
      (J := J X) (K := J Y) (L := J X)).symm
  let v : G ⋙ F ≅ 𝟭 (Sheaf (J Y) A) :=
    Functor.sheafPushforwardContinuousComp' (eFG := E.counitIso) (A := A)
      (J := J Y) (K := J X) (L := J Y)
  exact CategoryTheory.Equivalence.mk F G u v

def integersIso :
    (sheafEquivalence e).functor.obj ((constantSheaf (J X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))) ≅
      (constantSheaf (J Y) A).obj (AddCommGrpCat.of (ULift.{1} ℤ)) :=
  (restrictionConstantIso.{0} e.inv).app (AddCommGrpCat.of (ULift.{1} ℤ))

/-- The equivalence carries the actual continuous coefficient sheaf to itself. -/
def functionsIso (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    (sheafEquivalence e).functor.obj (functions M X) ≅ functions M Y :=
  (sheafToPresheaf (J Y) A).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V g
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp] <;> rfl))

end
end ManuscriptAudit.SchemeIsoProetaleSheaves

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SchemeIsoProetaleSheaves.sheafEquivalence,
      ``ManuscriptAudit.SchemeIsoProetaleSheaves.integersIso,
      ``ManuscriptAudit.SchemeIsoProetaleSheaves.functionsIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
