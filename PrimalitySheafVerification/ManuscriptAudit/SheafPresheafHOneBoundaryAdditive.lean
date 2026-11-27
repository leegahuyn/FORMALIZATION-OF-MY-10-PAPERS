import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! The actual connecting class of a section is additive. -/

namespace ManuscriptAudit.SheafPresheafHOneBoundaryAdditive

open CategoryTheory CategoryTheory.Abelian Opposite
open SheafPresheafHOneBoundary

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

private theorem sectionEquiv_eval (F : Sheaf J AddCommGrpCat.{v}) (U : C)
    (f : (freeYoneda J).obj U ⟶ F) :
    sectionEquiv J F U f =
      f.hom.app (op U) (sectionEquiv J ((freeYoneda J).obj U) U (𝟙 _)) := by
  let T := (freeYoneda J).obj U
  let q := sectionEquiv J T U (𝟙 T)
  have hq : sectionHom J T U q = 𝟙 T := (sectionEquiv J T U).symm_apply_apply _
  apply (sectionEquiv J F U).symm.injective
  change (sectionEquiv J F U).symm (sectionEquiv J F U f) =
    sectionHom J F U (f.hom.app (op U) q)
  rw [Equiv.symm_apply_apply, ← sectionHom_map, hq, Category.id_comp]

/-- The actual section representation is an additive equivalence. -/
def sectionAddEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeYoneda J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := sectionEquiv J F U
  map_add' f g := by
    change sectionEquiv J F U (f + g) = sectionEquiv J F U f + sectionEquiv J F U g
    rw [sectionEquiv_eval J F U (f + g), sectionEquiv_eval J F U f, sectionEquiv_eval J F U g]
    rfl

/-- The usual section boundary as an additive homomorphism. -/
def boundaryAddHom (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)
    (U : C) : S.X₃.obj.obj (op U) →+ S.X₁.H' 1 U :=
  (hS.extClass.postcomp ((freeYoneda J).obj U) rfl).comp
    (Ext.addEquiv₀.symm.toAddMonoidHom.comp (sectionAddEquiv J S.X₃ U).symm.toAddMonoidHom)

theorem boundaryAddHom_apply (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)
    (U : C) (s : S.X₃.obj.obj (op U)) :
    boundaryAddHom J S hS U s = boundaryOfSection J S hS U s := rfl

end
end ManuscriptAudit.SheafPresheafHOneBoundaryAdditive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafPresheafHOneBoundaryAdditive.sectionAddEquiv,
      ``ManuscriptAudit.SheafPresheafHOneBoundaryAdditive.boundaryAddHom_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
