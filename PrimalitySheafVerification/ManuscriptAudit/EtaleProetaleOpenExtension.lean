import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension

/-! Changing from the small étale site to the pro-étale site commutes
with actual extension by zero along an open immersion. -/

namespace ManuscriptAudit.EtaleProetaleOpenExtension

open AlgebraicGeometry CategoryTheory
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage directImage adjunction constantInverseImageIso)
open OpenEtaleExtension (etalePostcompose)
open OpenProetaleExtension (proetalePostcompose)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The two actual ways to view a small étale object over the open as a
pro-étale object over the ambient scheme agree. -/
def siteSquare : etalePostcompose j ⋙ inclusion X ≅ inclusion U ⋙ proetalePostcompose j :=
  NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl W.left) (by
    change 𝟙 W.left ≫ (W.hom ≫ j) = W.hom ≫ j
    simp)) (fun {W V} f ↦ by
    apply (Scheme.ProEt.forget X).map_injective
    apply Over.OverMorphism.ext
    change f.left ≫ 𝟙 V.left = 𝟙 W.left ≫ f.left
    simp)

private abbrev A := AddCommGrpCat.{u + 1}

private def restrictionSquare :
    directImage X ⋙ OpenEtaleExtension.restriction j A.{u} ≅
      OpenProetaleExtension.restriction j A.{u} ⋙ directImage U := by
  let E := etalePostcompose j
  let P := proetalePostcompose j
  let JU := U.smallEtaleTopology
  let JX := X.smallEtaleTopology
  let KU := Scheme.ProEt.topology U
  let KX := Scheme.ProEt.topology X
  letI : E.IsContinuous JU JX := OpenEtaleExtension.postcomposeContinuous j
  letI : P.IsContinuous KU KX := OpenProetaleExtension.postcomposeContinuous j
  letI := Functor.isContinuous_comp E (inclusion X) JU JX KX
  letI := Functor.isContinuous_comp (inclusion U) P JU KU KX
  let e₁ := Functor.sheafPushforwardContinuousComp (F := E) (G := inclusion X)
    (A := A.{u}) (J := JU) (K := JX) (L := KX)
  let e₂ := Functor.sheafPushforwardContinuousComp (F := inclusion U) (G := P)
    (A := A.{u}) (J := JU) (K := KU) (L := KX)
  exact e₁ ≪≫ Functor.sheafPushforwardContinuousIso (siteSquare j)
    (A := A.{u}) (J := JU) (K := KX) ≪≫ e₂.symm

/-- The actual étale inverse image commutes with the two native extension
by zero functors. -/
def extensionIso :
    OpenEtaleExtension.extensionByZero j A.{u} ⋙ inverseImage X ≅
      inverseImage U ⋙ OpenProetaleExtension.extensionByZero j A.{u} :=
  let a := (OpenEtaleExtension.extensionByZeroAdjunction j A.{u}).comp (adjunction X)
  let b := (adjunction U).comp (OpenProetaleExtension.extensionByZeroAdjunction j A.{u})
  (a.ofNatIsoRight (restrictionSquare j)).leftAdjointUniq b

/-- In particular this identifies extension by zero of actual constant
coefficient sheaves after changing sites. -/
def constantExtensionIso (M : A.{u}) :
    (inverseImage X).obj ((OpenEtaleExtension.extensionByZero j A.{u}).obj
      ((constantSheaf U.smallEtaleTopology A.{u}).obj M)) ≅
    (OpenProetaleExtension.extensionByZero j A.{u}).obj
      ((constantSheaf (Scheme.ProEt.topology U) A.{u}).obj M) :=
  (extensionIso j).app _ ≪≫
    (OpenProetaleExtension.extensionByZero j A.{u}).mapIso ((constantInverseImageIso U).app M)

end
end ManuscriptAudit.EtaleProetaleOpenExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleOpenExtension.siteSquare,
      ``ManuscriptAudit.EtaleProetaleOpenExtension.extensionIso,
      ``ManuscriptAudit.EtaleProetaleOpenExtension.constantExtensionIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
