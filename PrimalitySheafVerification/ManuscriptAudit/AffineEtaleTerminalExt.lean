import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDerivedRestriction

/-! The Ext-degree-zero representative of the actual affine section restriction. -/

namespace ManuscriptAudit.AffineEtaleTerminalExt

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction AffineEtaleRestrictionNaturality AffineEtaleDerivedRestriction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev C (R : Type) [CommRing R] := Sheaf (J R) AddCommGrpCat.{0}
private abbrev terminal (R : Type) [CommRing R] :=
  KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

abbrev constantInteger (R : Type) [CommRing R] :=
  (constantSheaf (J R) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The genuine map from the constant integers associated with a global section. -/
def sectionHom (R : Type) [CommRing R] (F : C R)
    (x : F.obj.obj (op (baseObject R))) : constantInteger R ⟶ F :=
  Ext.homEquiv₀ ((Sheaf.H.equiv₀ F (terminal R)).symm x)

theorem mk₀_sectionHom (R : Type) [CommRing R] (F : C R)
    (x : F.obj.obj (op (baseObject R))) :
    Ext.mk₀ (sectionHom R F x) = (Sheaf.H.equiv₀ F (terminal R)).symm x :=
  Ext.mk₀_homEquiv₀_apply _

private theorem sectionHom_map (R : Type) [CommRing R]
    {F G : C R} (f : F ⟶ G) (x : F.obj.obj (op (baseObject R))) :
    sectionHom R G (f.hom.app (op (baseObject R)) x) = sectionHom R F x ≫ f := by
  apply (Ext.mk₀_bijective (constantInteger R) G).injective
  rw [mk₀_sectionHom, ← Ext.mk₀_comp_mk₀, mk₀_sectionHom]
  exact (Sheaf.H.equiv₀_symm_naturality (terminal R) f x).symm

private def generator (R : Type) [CommRing R] :
    (constantInteger R).obj.obj (op (baseObject R)) :=
  Sheaf.H.equiv₀ (constantInteger R) (terminal R) (Ext.mk₀ (𝟙 (constantInteger R)))

private theorem sectionHom_eval (R : Type) [CommRing R] (F : C R)
    (x : F.obj.obj (op (baseObject R))) :
    (sectionHom R F x).hom.app (op (baseObject R)) (generator R) = x := by
  have hg : sectionHom R (constantInteger R) (generator R) = 𝟙 _ := by
    apply (Ext.mk₀_bijective (constantInteger R) (constantInteger R)).injective
    rw [mk₀_sectionHom, generator, AddEquiv.symm_apply_apply]
  apply (Sheaf.H.equiv₀ F (terminal R)).symm.injective
  rw [← mk₀_sectionHom, sectionHom_map, hg, Category.id_comp, mk₀_sectionHom]

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]

/-- Actual section restriction and subsequent application of a sheaf map
correspond to composing the genuine maps in Ext degree zero. -/
theorem sectionHom_restrict {F : C A} {G : C S}
    (g : (affineRestriction (i A S)).obj F ⟶ G) (x : F.obj.obj (op (baseObject A))) :
    sectionHom S G (g.hom.app (op (baseObject S))
      ((restrictSection (i A S) F (baseMap A S)).hom x)) =
    restrictionConstant A S ≫ (affineRestriction (i A S)).map (sectionHom A F x) ≫ g := by
  let f := sectionHom A F x
  let b := baseMap A S
  have h := congrArg (fun k : (constantInteger A).obj.obj (op (baseObject A)) ⟶
      ((affineRestriction (i A S)).obj F).obj.obj (op (baseObject S)) =>
        k.hom (generator A)) (restrictSection_sheafMap (i A S) f b)
  simp only [ConcreteCategory.comp_apply] at h
  rw [sectionHom_eval] at h
  have hc : restrictionConstant A S = sectionHom S _
      ((restrictSection (i A S) (constantInteger A) b).hom (generator A)) := rfl
  rw [sectionHom_map, h, sectionHom_map, hc, Category.assoc]

end

end ManuscriptAudit.AffineEtaleTerminalExt

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleTerminalExt.sectionHom_restrict
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
