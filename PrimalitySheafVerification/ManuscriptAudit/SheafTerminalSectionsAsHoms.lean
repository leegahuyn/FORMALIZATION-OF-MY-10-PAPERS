import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! The actual natural additive identification of terminal sections with maps from the constant integers. -/

namespace ManuscriptAudit.SheafTerminalSectionsAsHoms

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}

variable [HasSheafify J A]

/-- The actual constant integer sheaf used as source of native sheaf Ext. -/
abbrev integers := (constantSheaf J A).obj (AddCommGrpCat.of (ULift.{0} ℤ))

/-- Actual evaluation of an abelian sheaf at a site object. -/
abbrev sections (T : C) : Sheaf J A ⥤ A := (sheafSections J A).obj (op T)

variable {T : C} (hT : IsTerminal T)

/-- A homomorphism from the constant integers is identified with its terminal section at 1. -/
def homEquiv (F : Sheaf J A) : (integers J ⟶ F) ≃+ (sections J T).obj F :=
  ((constantSheafAdj J A hT).homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

theorem homEquiv_comp {F G : Sheaf J A} (f : integers J ⟶ F) (g : F ⟶ G) :
    homEquiv J hT G (f ≫ g) = (sections J T).map g (homEquiv J hT F f) := by
  let a := constantSheafAdj J A hT
  change (a.homEquiv _ _ (f ≫ g)).hom ⟨1⟩ =
    (sections J T).map g ((a.homEquiv _ _ f).hom ⟨1⟩)
  rw [a.homEquiv_naturality_right] <;> rfl

theorem homEquiv_symm_map {F G : Sheaf J A} (f : F ⟶ G)
    (x : (sections J T).obj F) :
    (homEquiv J hT G).symm ((sections J T).map f x) = (homEquiv J hT F).symm x ≫ f := by
  apply (homEquiv J hT G).injective
  rw [AddEquiv.apply_symm_apply, homEquiv_comp, AddEquiv.apply_symm_apply]

end
end ManuscriptAudit.SheafTerminalSectionsAsHoms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafTerminalSectionsAsHoms.homEquiv,
      ``ManuscriptAudit.SheafTerminalSectionsAsHoms.homEquiv_comp,
      ``ManuscriptAudit.SheafTerminalSectionsAsHoms.homEquiv_symm_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
