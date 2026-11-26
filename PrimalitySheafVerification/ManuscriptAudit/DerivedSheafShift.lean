import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree shifts in native derived sheaf hypercohomology

The actual derived-category Hom from the free rank-one constant sheaf
recovers the usual degree-zero sections. A sheaf placed in degree one
therefore has nonzero first hypercohomology whenever it has nonzero
global sections. Finiteness of the support does not alter this calculation.
-/

namespace ManuscriptAudit.DerivedSheafShift

open CategoryTheory CategoryTheory.Abelian Opposite

universe u v w wH wD

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasDerivedCategory.{wD} (Sheaf J AddCommGrpCat.{w})]
variable [HasExt.{wH} (Sheaf J AddCommGrpCat.{w})]

noncomputable section

/-- Hypercohomology represented by the native derived category of abelian sheaves. -/
abbrev hyperH (K : DerivedCategory (Sheaf J AddCommGrpCat.{w})) (n : ℤ) :=
  (DerivedCategory.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0).obj
    ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) ⟶ K⟦n⟧

/-- A sheaf, regarded as a complex concentrated in cohomological degree one. -/
abbrev degreeOne (F : Sheaf J AddCommGrpCat.{w}) :=
  (DerivedCategory.singleFunctor (Sheaf J AddCommGrpCat.{w}) (1 : ℤ)).obj F

/-- First hypercohomology of the shifted sheaf is the original degree-zero cohomology. -/
def degreeOne_hyperH_equiv (F : Sheaf J AddCommGrpCat.{w}) :
    hyperH J (degreeOne J F) 1 ≃ Sheaf.H F 0 := by
  let S := Sheaf J AddCommGrpCat.{w}
  let single := DerivedCategory.singleFunctor S 0
  let e : (degreeOne J F)⟦(1 : ℤ)⟧ ≅ single.obj F :=
    ((DerivedCategory.singleFunctors S).shiftIso 1 0 1 (by decide)).app F
  let f : single.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  exact e.homToEquiv.trans (f.homEquiv.symm.trans Ext.homEquiv₀.symm)

/-- An actual nonzero global section yields positive-degree hypercohomology after shifting. -/
theorem degreeOne_hyperH_not_subsingleton (F : Sheaf J AddCommGrpCat.{w})
    {T : C} (hT : Limits.IsTerminal T) (h : ¬ Subsingleton (F.obj.obj (op T))) :
    ¬ Subsingleton (hyperH J (degreeOne J F) 1) := by
  let e := (degreeOne_hyperH_equiv J F).trans (Sheaf.H.equiv₀ F hT).toEquiv
  intro hH
  exact h ⟨fun x y => e.symm.injective (hH.elim (e.symm x) (e.symm y))⟩

end

end ManuscriptAudit.DerivedSheafShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.DerivedSheafShift.degreeOne_hyperH_equiv,
      ``ManuscriptAudit.DerivedSheafShift.degreeOne_hyperH_not_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
