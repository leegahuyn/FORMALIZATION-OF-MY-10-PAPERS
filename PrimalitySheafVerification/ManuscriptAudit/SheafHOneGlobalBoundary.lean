import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# A non-liftable global quotient section gives nonzero H¹

This transports the exact connecting map through the native
identification of H⁰ with sections at a terminal object.
-/

namespace ManuscriptAudit.SheafHOneGlobalBoundary

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private noncomputable abbrev integerConstant : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

theorem hOne_nontrivial_of_unlifted_global_section
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (z : S.X₃.obj.obj (op T))
    (hz : ¬ ∃ y : S.X₂.obj.obj (op T), S.g.hom.app (op T) y = z) :
    Nontrivial (Sheaf.H S.X₁ 1) := by
  let δ := hS.extClass.postcomp (integerConstant (J := J)) (show 0 + 1 = 1 by rfl)
  let c := δ ((Sheaf.H.equiv₀ S.X₃ hT).symm z)
  refine ⟨⟨c, 0, ?_⟩⟩
  intro hc
  have exactness := Ext.covariant_sequence_exact₃' (integerConstant (J := J)) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at exactness
  obtain ⟨y, hy⟩ := (exactness ((Sheaf.H.equiv₀ S.X₃ hT).symm z)).1 hc
  apply hz
  refine ⟨(Sheaf.H.equiv₀ S.X₂ hT) y, ?_⟩
  apply (Sheaf.H.equiv₀ S.X₃ hT).symm.injective
  rw [← Sheaf.H.equiv₀_symm_naturality (hT := hT) S.g, AddEquiv.symm_apply_apply]
  exact hy

end ManuscriptAudit.SheafHOneGlobalBoundary

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafHOneGlobalBoundary.hOne_nontrivial_of_unlifted_global_section
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
