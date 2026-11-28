import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-! The literal restriction of a section between nested ambient étale
objects agrees with restriction after moving to the larger open site. -/

namespace ManuscriptAudit.NestedOpenEtaleSectionNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension OpenEtaleHOneByRepresentatives EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
private abbrev A := AddCommGrpCat.{u}

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]

/-- The literal morphism of small étale objects associated to the nested opens. -/
def nestedObjectArrow : Scheme.Etale.mk (i ≫ j) ⟶ Scheme.Etale.mk j :=
  MorphismProperty.Over.homMk i rfl

private abbrev terminal (Y : Scheme.{u}) := identityObject Y

private def openObjectIso {Y Z : Scheme.{u}} (a : Y ⟶ Z) [IsOpenImmersion a] :
    (etalePostcompose a).obj (terminal Y) ≅ Scheme.Etale.mk a :=
  MorphismProperty.Over.isoMk (Iso.refl Y) (by rfl)

private abbrev composeIso :
    etalePostcompose (i ≫ j) ≅ etalePostcompose i ⋙ etalePostcompose j :=
  MorphismProperty.Over.mapComp (P := @AlgebraicGeometry.Etale) ⊤
    (show Etale i from inferInstance) (show Etale j from inferInstance)

private theorem actual_arrows_compose :
    ((composeIso i j).hom.app (terminal V)) ≫
      (etalePostcompose j).map (openObjectIso i).hom ≫
      (etalePostcompose j).map (openArrow i) ≫ (openObjectIso j).hom =
    (openObjectIso (i ≫ j)).hom ≫ nestedObjectArrow i j := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 V ≫ 𝟙 V ≫ i ≫ 𝟙 U = 𝟙 V ≫ i
  simp

variable (F : Sheaf X.smallEtaleTopology A.{u})

private theorem sections_comp {P Q R : X.Etale} (a : P ⟶ Q) (b : Q ⟶ R) (x : F.obj.obj (op R)) :
    F.obj.map a.op (F.obj.map b.op x) = F.obj.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Actual global sections restricted between the two ambient étale
objects agree with the literal open-site restriction and its composition. -/
theorem sectionEquiv_nested (x : F.obj.obj (op (Scheme.Etale.mk j))) :
    ((restrictionCompIso i j).hom.app F).hom.app (op (terminal V))
      (sectionEquiv i ((restriction j A.{u}).obj F)
        (((restriction j A.{u}).obj F).obj.map (openArrow i).op (sectionEquiv j F x))) =
    sectionEquiv (i ≫ j) F (F.obj.map (nestedObjectArrow i j).op x) := by
  let a := ((composeIso i j).hom.app (terminal V))
  let b := (etalePostcompose j).map (openObjectIso i).hom
  let c := (etalePostcompose j).map (openArrow i)
  let d := (openObjectIso j).hom
  let e := (openObjectIso (i ≫ j)).hom
  let f := nestedObjectArrow i j
  change F.obj.map a.op (F.obj.map b.op (F.obj.map c.op (F.obj.map d.op x))) =
    F.obj.map e.op (F.obj.map f.op x)
  rw [sections_comp F c d, sections_comp F b (c ≫ d),
    sections_comp F a (b ≫ c ≫ d), sections_comp F e f]
  exact congrArg (fun g : (etalePostcompose (i ≫ j)).obj (terminal V) ⟶
    Scheme.Etale.mk j => F.obj.map g.op x) (actual_arrows_compose i j)

end

end ManuscriptAudit.NestedOpenEtaleSectionNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NestedOpenEtaleSectionNaturality.sectionEquiv_nested
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
