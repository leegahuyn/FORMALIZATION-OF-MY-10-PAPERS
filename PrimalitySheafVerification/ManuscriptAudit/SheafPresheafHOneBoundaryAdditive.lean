import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! The actual degree-one boundary of sections is an additive homomorphism. -/

namespace ManuscriptAudit.SheafPresheafHOneBoundary

open CategoryTheory CategoryTheory.Abelian Opposite

noncomputable section
universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem sectionEquiv_eval (F : Sheaf J AddCommGrpCat.{v}) (U : C)
    (a : (freeYoneda J).obj U ⟶ F) :
    sectionEquiv J F U a =
      a.hom.app (op U) (sectionEquiv J ((freeYoneda J).obj U) U (𝟙 _)) := by
  let Y := (freeYoneda J).obj U
  let y := sectionEquiv J Y U (𝟙 Y)
  have h := sectionHom_map J a U y
  change (sectionEquiv J Y U).symm (sectionEquiv J Y U (𝟙 Y)) ≫ a =
    (sectionEquiv J F U).symm (a.hom.app (op U) y) at h
  rw [Equiv.symm_apply_apply, Category.id_comp] at h
  apply (sectionEquiv J F U).symm.injective
  rw [Equiv.symm_apply_apply]
  exact h

private theorem sectionHom_add (F : Sheaf J AddCommGrpCat.{v}) (U : C)
    (a b : F.obj.obj (op U)) :
    sectionHom J F U (a + b) = sectionHom J F U a + sectionHom J F U b := by
  have h (f g : (freeYoneda J).obj U ⟶ F) :
      sectionEquiv J F U (f + g) = sectionEquiv J F U f + sectionEquiv J F U g := by
    simp only [sectionEquiv_eval J F U]
    rfl
  apply (sectionEquiv J F U).injective
  change (sectionEquiv J F U) ((sectionEquiv J F U).symm (a + b)) =
    (sectionEquiv J F U) ((sectionEquiv J F U).symm a + (sectionEquiv J F U).symm b)
  rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Native Kummer and sheaf boundary classes are additive in the input section. -/
def boundaryAddHom (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact) (U : C) :
    (S.X₃.obj.obj (op U)) →+ S.X₁.H' 1 U where
  toFun := boundaryOfSection J S hS U
  map_zero' := (boundaryOfSection_eq_zero_iff J S hS U 0).mpr ⟨0, map_zero _⟩
  map_add' a b := by
    simp only [boundaryOfSection, sectionHom_add J, Ext.mk₀_add, Ext.add_comp]
 
/-- The native boundary is onto if the middle degree-one cohomology vanishes on the chart. -/
theorem boundaryAddHom_surjective (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) (U : C) (hMiddle : Subsingleton (S.X₂.H' 1 U)) :
    Function.Surjective (boundaryAddHom J S hS U) := by
  intro c
  have hz₀ : c.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := hMiddle.elim _ _
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ ((freeYoneda J).obj U) hS c
    hz₀ (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) S.X₃).surjective z
  refine ⟨sectionEquiv J S.X₃ U f, ?_⟩
  change (Ext.mk₀ ((sectionEquiv J S.X₃ U).symm (sectionEquiv J S.X₃ U f))).comp
    hS.extClass rfl = _
  rw [Equiv.symm_apply_apply]
  exact hz

end
end ManuscriptAudit.SheafPresheafHOneBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafPresheafHOneBoundary.boundaryAddHom,
      ``ManuscriptAudit.SheafPresheafHOneBoundary.boundaryAddHom_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
