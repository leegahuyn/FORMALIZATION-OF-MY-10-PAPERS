import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Data.DFinsupp.Module

/-!
# Finite-support families of additive presheaves

Sections are dependent finitely supported functions. Restriction is
componentwise and hence keeps finite support.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open CategoryTheory Opposite

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {ι : Type}
  (P : ι → Cᵒᵖ ⥤ AddCommGrpCat.{0})

/-- The actual pointwise direct sum of additive presheaves. -/
def directSum : Cᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj X := AddCommGrpCat.of (Π₀ a, (P a).obj X)
  map f := AddCommGrpCat.ofHom (DFinsupp.mapRange.addMonoidHom fun a ↦ ((P a).map f).hom)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro z
    apply DFinsupp.ext
    intro a
    change (P a).map (𝟙 X) (z a) = z a
    rw [Functor.map_id, ConcreteCategory.id_apply]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    apply DFinsupp.ext
    intro a
    change (P a).map (f ≫ g) (z a) = (P a).map g ((P a).map f (z a))
    rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- Evaluation at one component commutes with all restrictions. -/
def component (a : ι) : directSum P ⟶ P a where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z a
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

@[simp] theorem directSum_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : (directSum P).obj X) (a : ι) :
    ((directSum P).map f z) a = (P a).map f (z a) := rfl

@[simp] theorem component_app_apply (a : ι) (X : Cᵒᵖ) (z : (directSum P).obj X) :
    (component P a).app X z = z a := rfl

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteSupportPresheaf.directSum,
      ``ManuscriptAudit.FiniteSupportPresheaf.component] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
