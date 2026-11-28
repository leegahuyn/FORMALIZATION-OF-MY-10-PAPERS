import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TerminalCohomologySectionHom
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSheafification
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives

/-! Genuine open restriction transports the actual constant-integer
morphism that represents each literal global section. -/

namespace ManuscriptAudit.OpenEtaleTerminalSectionHom

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TerminalCohomologySectionHom OpenEtaleExtension OpenEtaleSheafification
open OpenEtaleHOneByRepresentatives EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u}
private abbrev J (Y : Scheme.{u}) := Y.smallEtaleTopology
private abbrev R := restriction j A.{u}
private abbrev T (Y : Scheme.{u}) := identityObject Y
private abbrev t (Y : Scheme.{u}) := MorphismProperty.Over.mkIdTerminal @Etale Y
private abbrev C (Y : Scheme.{u}) := Sheaf (J Y) A.{u}
private abbrev Z (Y : Scheme.{u}) := integerSheaf (J Y)
private abbrev s (Y : Scheme.{u}) := sheafificationAdjunction (J Y) A.{u}

/-- The genuine restriction of the constant integer sheaf. -/
def constantIntegerIso : Z U ≅ (R j).obj (Z X) :=
  (comparison j).app (integerPresheaf (D := X.Etale))

variable (F : C X)

/-- Restriction of the actual terminal section along the open immersion. -/
def restrictSection (x : F.obj.obj (op (T X))) :
    ((R j).obj F).obj.obj (op (T U)) :=
  sectionEquiv j F (F.obj.map (openArrow j).op x)

private theorem section_of_terminal (x : F.obj.obj (op (T X))) :
    F.obj.map ((t X).from ((etalePostcompose j).obj (T U))).op x = restrictSection j F x := by
  let O := (etalePostcompose j).obj (T U)
  let a : O ≅ Scheme.Etale.mk j := MorphismProperty.Over.isoMk (Iso.refl U) (by rfl)
  have h : a.hom ≫ openArrow j = (t X).from O := (t X).hom_ext _ _
  change F.obj.map ((t X).from O).op x = F.obj.map a.hom.op (F.obj.map (openArrow j).op x)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h]

/-- The literal restriction of a terminal section corresponds to composing
its representing constant-integer morphism with the genuine comparison. -/
theorem sectionHom_restrict (x : F.obj.obj (op (T X))) :
    sectionHom (J U) (t U) ((R j).obj F) (restrictSection j F x) =
      (constantIntegerIso j).hom ≫ (R j).map (sectionHom (J X) (t X) F x) := by
  let f := sectionHom (J X) (t X) F x
  let p := presheafHom (J X) F f
  let Q := (R j).obj F
  let g := (constantIntegerIso j).hom ≫ (R j).map f
  have hp : ((s X).homEquiv (integerPresheaf (D := X.Etale)) F).symm p = f :=
    ((s X).homEquiv (integerPresheaf (D := X.Etale)) F).symm_apply_apply f
  have h := comparison_postcompose j (integerPresheaf (D := X.Etale)) F p
  rw [hp] at h
  change presheafHom (J U) Q g = (precompose j).map p at h
  have hv := congrArg (fun a : integerPresheaf (D := U.Etale) ⟶ Q.obj =>
    a.app (op (T U)) (ULift.up 1)) h
  change (presheafHom (J U) Q g).app (op (T U)) (ULift.up 1) =
    p.app (op ((etalePostcompose j).obj (T U))) (ULift.up 1) at hv
  apply (Ext.mk₀_bijective (Z U) Q).injective
  apply (Sheaf.H.equiv₀ Q (t U)).injective
  rw [mk₀_sectionHom, AddEquiv.apply_symm_apply, evaluate_hom]
  exact (hv.trans ((sectionHom_evaluation (J X) (t X) F x _).trans
    (section_of_terminal j F x))).symm

end

end ManuscriptAudit.OpenEtaleTerminalSectionHom

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleTerminalSectionHom.sectionHom_restrict
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
