import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! The zero-degree native cohomology presheaf is evaluation on the
underlying sheaf, with genuine restriction maps. -/

namespace ManuscriptAudit.EtaleCohomologyPresheafZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u

private abbrev A := AddCommGrpCat.{u}

private abbrev adj (X : Scheme.{u}) :=
  (Adjunction.whiskerRight X.Etaleᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction X.smallEtaleTopology A.{u})

variable {X : Scheme.{u}}

private def homSections (U : X.Etale) (F : Sheaf X.smallEtaleTopology A.{u}) :
    ((freeEtaleRepresentable X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((adj X).homEquiv (yoneda.obj U) F).trans yonedaEquiv

private theorem homSections_postcompose (U : X.Etale) {F G : Sheaf X.smallEtaleTopology A.{u}}
    (f : (freeEtaleRepresentable X).obj U ⟶ F) (g : F ⟶ G) :
    homSections U G (f ≫ g) = g.hom.app (op U) (homSections U F f) := by
  let a := adj X
  change yonedaEquiv ((a.homEquiv (yoneda.obj U) G) (f ≫ g)) =
    g.hom.app (op U) (yonedaEquiv ((a.homEquiv (yoneda.obj U) F) f))
  rw [a.homEquiv_naturality_right, yonedaEquiv_comp] <;> rfl

private theorem homSections_precompose {U V : X.Etale} (f : U ⟶ V)
    {F : Sheaf X.smallEtaleTopology A.{u}} (h : (freeEtaleRepresentable X).obj V ⟶ F) :
    homSections U F ((freeEtaleRepresentable X).map f ≫ h) =
      F.obj.map f.op (homSections V F h) := by
  let a := adj X
  change yonedaEquiv ((a.homEquiv (yoneda.obj U) F) (_ ≫ h)) =
    F.obj.map f.op (yonedaEquiv ((a.homEquiv (yoneda.obj V) F) h))
  rw [a.homEquiv_naturality_left (yoneda.map f)]
  exact (yonedaEquiv_naturality _ f).symm

private def generator (U : X.Etale) :
    ((freeEtaleRepresentable X).obj U).obj.obj (op U) :=
  homSections U ((freeEtaleRepresentable X).obj U) (𝟙 _)

private theorem homSections_apply (U : X.Etale) (F : Sheaf X.smallEtaleTopology A.{u})
    (f : (freeEtaleRepresentable X).obj U ⟶ F) :
    homSections U F f = f.hom.app (op U) (generator U) := by
  simpa only [Category.id_comp] using homSections_postcompose U (𝟙 _) f

/-- The zero-degree native Ext definition evaluates the sheaf at the object. -/
def equivZero (F : Sheaf X.smallEtaleTopology A.{u}) (U : X.Etale) :
    F.H' 0 U ≃+ F.obj.obj (op U) where
  toEquiv := Ext.addEquiv₀.toEquiv.trans (homSections U F)
  map_add' x y := by
    change homSections U F (Ext.addEquiv₀ (x + y)) =
      homSections U F (Ext.addEquiv₀ x) + homSections U F (Ext.addEquiv₀ y)
    rw [map_add]
    simp only [homSections_apply] <;> rfl

/-- The map of the native zero-degree cohomology presheaf is the actual
restriction morphism of the sheaf. -/
theorem equivZero_natural (F : Sheaf X.smallEtaleTopology A.{u}) {U V : X.Etale}
    (f : U ⟶ V) (x : F.H' 0 V) :
    equivZero F U ((F.cohomologyPresheaf 0).map f.op x) =
      F.obj.map f.op (equivZero F V x) := by
  have h : Ext.addEquiv₀ ((F.cohomologyPresheaf 0).map f.op x) =
      (freeEtaleRepresentable X).map f ≫ Ext.addEquiv₀ x := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply] <;> rfl
  change homSections U F (Ext.addEquiv₀ ((F.cohomologyPresheaf 0).map f.op x)) =
    F.obj.map f.op (homSections V F (Ext.addEquiv₀ x))
  rw [h]
  exact homSections_precompose f _

/-- At a small étale object the actual units give the zero-degree cohomology value. -/
def unitEquivZero {X : Scheme.{0}} (U : X.Etale) :
    (KummerUnitsSheaf.fullCoordinateUnitSheaf X).H' 0 U ≃+ Additive (Γ(U.left, ⊤))ˣ :=
  equivZero (KummerUnitsSheaf.fullCoordinateUnitSheaf X) U

/-- The zero-degree étale cohomology restrictions are the actual ring-unit maps. -/
theorem unitEquivZero_natural {X : Scheme.{0}} {U V : X.Etale} (f : U ⟶ V)
    (a : (KummerUnitsSheaf.fullCoordinateUnitSheaf X).H' 0 V) :
    unitEquivZero U (((KummerUnitsSheaf.fullCoordinateUnitSheaf X).cohomologyPresheaf 0).map f.op a) =
      Additive.ofMul (Units.map f.left.appTop.hom.toMonoidHom (unitEquivZero V a).toMul) :=
  equivZero_natural (KummerUnitsSheaf.fullCoordinateUnitSheaf X) f a

end

end ManuscriptAudit.EtaleCohomologyPresheafZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCohomologyPresheafZero.equivZero,
      ``ManuscriptAudit.EtaleCohomologyPresheafZero.equivZero_natural,
      ``ManuscriptAudit.EtaleCohomologyPresheafZero.unitEquivZero_natural] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
