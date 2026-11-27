import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! Dimension shifting along an actual short exact sequence of abelian sheaves. -/

namespace ManuscriptAudit.SheafCohomologyDimensionShift

open CategoryTheory CategoryTheory.Abelian

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- With injective middle term, vanishing cohomology of the quotient
implies vanishing in the next degree for the first term. -/
theorem H_succ_subsingleton_of_injectiveMiddle
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact) [Injective S.X₂]
    (n : ℕ) (h : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  let Z := (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))
  apply subsingleton_of_forall_eq 0
  intro x
  change Ext Z S.X₁ (n + 1) at x
  have hx : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (show n + 1 = n + 1 by rfl)
  have hzero : y = 0 := h.elim _ _
  change x = 0
  rw [← hy, hzero, Ext.zero_comp]

end ManuscriptAudit.SheafCohomologyDimensionShift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
