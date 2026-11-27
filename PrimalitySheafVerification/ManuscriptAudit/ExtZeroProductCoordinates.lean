import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Abelian.Basic

/-! Native Ext in degree zero of a binary product has its literal two
coordinate projections. -/

namespace ManuscriptAudit.ExtZeroProductCoordinates

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (T F G : C)

private def homEquiv : (T ⟶ F ⨯ G) ≃+ (T ⟶ F) × (T ⟶ G) where
  toFun f := (f ≫ prod.fst, f ≫ prod.snd)
  invFun p := prod.lift p.1 p.2
  left_inv f := by apply prod.hom_ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  map_add' f g := by
    apply Prod.ext
    · simp only [Preadditive.add_comp, Prod.fst_add]
    · simp only [Preadditive.add_comp, Prod.snd_add]

/-- Standard degree-zero product coordinates on the genuine Ext groups. -/
def equiv : Ext.{w} T (F ⨯ G) 0 ≃+ Ext.{w} T F 0 × Ext.{w} T G 0 :=
  Ext.addEquiv₀.trans ((homEquiv T F G).trans (Ext.addEquiv₀.symm.prodCongr Ext.addEquiv₀.symm))

theorem fst_apply (x : Ext.{w} T (F ⨯ G) 0) :
    (equiv T F G x).1 = x.comp (Ext.mk₀ (prod.fst : F ⨯ G ⟶ F)) (add_zero 0) := by
  change Ext.mk₀ (Ext.addEquiv₀ x ≫ (prod.fst : F ⨯ G ⟶ F)) = _
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

theorem snd_apply (x : Ext.{w} T (F ⨯ G) 0) :
    (equiv T F G x).2 = x.comp (Ext.mk₀ (prod.snd : F ⨯ G ⟶ G)) (add_zero 0) := by
  change Ext.mk₀ (Ext.addEquiv₀ x ≫ (prod.snd : F ⨯ G ⟶ G)) = _
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

end

end ManuscriptAudit.ExtZeroProductCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExtZeroProductCoordinates.fst_apply,
      ``ManuscriptAudit.ExtZeroProductCoordinates.snd_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
