import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Additive
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage

/-! Native pro-étale degree-zero cohomology of a direct image agrees
naturally with the actual degree-zero cohomology on its source. -/

namespace ManuscriptAudit.ProetaleDirectImageHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev Z (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

private abbrev G := directImage f A
private abbrev L := inverseImage f

private def constantIso : (L f).obj (Z X) ≅ Z Y :=
  (constantInverseImageIso f).app (AddCommGrpCat.of (ULift.{1} ℤ))

private def homSource (F : C Y) : ((L f).obj (Z X) ⟶ F) ≃+ (Z Y ⟶ F) where
  toFun a := (constantIso f).inv ≫ a
  invFun a := (constantIso f).hom ≫ a
  left_inv _ := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv _ := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_add' _ _ := Preadditive.comp_add _ _ _

/-- The degree-zero comparison is precisely the adjunction on the native
constant integer object representing sections. -/
def equivalence (F : C Y) : Sheaf.H ((G f).obj F) 0 ≃+ Sheaf.H F 0 :=
  Ext.addEquiv₀.trans (((adjunction f).homAddEquiv (Z X) F).symm.trans
    ((homSource f F).trans Ext.addEquiv₀.symm))

theorem equivalence_mk (F : C Y) (a : Z X ⟶ (G f).obj F) :
    equivalence f F (Ext.mk₀ a) =
      Ext.mk₀ ((constantIso f).inv ≫ ((adjunction f).homEquiv (Z X) F).symm a) := by
  have ha : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  change Ext.mk₀ ((constantIso f).inv ≫
    ((adjunction f).homEquiv (Z X) F).symm (Ext.addEquiv₀ (Ext.mk₀ a))) = _
  rw [ha]

/-- The two degree-zero functors agree on every actual coefficient arrow. -/
theorem natural {F F' : C Y} (g : F ⟶ F') (x : Sheaf.H ((G f).obj F) 0) :
    equivalence f F' (Sheaf.H.map ((G f).map g) 0 x) =
      Sheaf.H.map g 0 (equivalence f F x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective (Z X) ((G f).obj F)).surjective x
  have hg : Sheaf.H.map ((G f).map g) 0 (Ext.mk₀ a) =
      Ext.mk₀ (a ≫ (G f).map g) := Ext.mk₀_comp_mk₀ _ _
  rw [hg, equivalence_mk, equivalence_mk]
  change Ext.mk₀ ((constantIso f).inv ≫ ((adjunction f).homEquiv (Z X) F').symm
    (a ≫ (G f).map g)) = (Ext.mk₀ ((constantIso f).inv ≫
      ((adjunction f).homEquiv (Z X) F).symm a)).comp (Ext.mk₀ g) rfl
  rw [Ext.mk₀_comp_mk₀, (adjunction f).homEquiv_naturality_right_symm, Category.assoc]

end
end ManuscriptAudit.ProetaleDirectImageHZero

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleDirectImageHZero.natural
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
