import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Grp.Limits

/-! A section of a categorical product of additive sheaves is determined
by its two genuine component sections. -/

namespace ManuscriptAudit.SheafProductSectionExt

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J AddCommGrpCat.{w}}

theorem section_ext (T : Cᵒᵖ) (x y : (F ⨯ G).obj.obj T)
    (h₀ : (prod.fst : F ⨯ G ⟶ F).hom.app T x = (prod.fst : F ⨯ G ⟶ F).hom.app T y)
    (h₁ : (prod.snd : F ⨯ G ⟶ G).hom.app T x = (prod.snd : F ⨯ G ⟶ G).hom.app T y) :
    x = y := by
  let A := AddCommGrpCat.{w}
  let E := sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj T ⋙ forget A
  let f : ULift.{w} Unit ⟶ E.obj (F ⨯ G) := TypeCat.ofHom (fun _ ↦ x)
  let g : ULift.{w} Unit ⟶ E.obj (F ⨯ G) := TypeCat.ofHom (fun _ ↦ y)
  let hE := isLimitOfHasBinaryProductOfPreservesLimit E F G
  have h : f = g := BinaryFan.IsLimit.hom_ext hE (by
    apply ConcreteCategory.hom_ext
    intro z
    exact h₀) (by
    apply ConcreteCategory.hom_ext
    intro z
    exact h₁)
  exact ConcreteCategory.congr_hom h (⟨()⟩ : ULift.{w} Unit)

end

end ManuscriptAudit.SheafProductSectionExt

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafProductSectionExt.section_ext
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
