import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorDerivedAdjunction

/-!
# Ext adjunction for exact additive adjoints

The derived adjunction and its comparison isomorphisms with single
complexes and shifts identify the native Ext groups in every degree.
-/

namespace ManuscriptAudit.ExactFunctorDerivedAdjunction

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def morphismAddEquiv {C : Type*} [Category* C] [Preadditive C]
    {A A' B B' : C} (e : A ≅ A') (f : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toFun g := e.inv ≫ g ≫ f.hom
  invFun g := e.hom ≫ g ≫ f.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := by simp [Preadditive.comp_add, Preadditive.add_comp]

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasExt C] [HasExt D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The ordinary adjunction of exact additive functors induces an additive
adjunction on their native Ext groups in every nonnegative degree. -/
def extAdjunction (a : F ⊣ G) (A : C) (B : D) (n : ℕ) :
    Ext (F.obj A) B n ≃+ Ext A (G.obj B) n := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  let l := F.mapDerivedCategory
  let r := G.mapDerivedCategory
  letI : l.Additive := mapDerivedCategory_additive (F := F)
  let e := derivedAdjunction a
  let A₀ := (DerivedCategory.singleFunctor C 0).obj A
  let B₀ := (DerivedCategory.singleFunctor D 0).obj B
  let e₁ : l.obj A₀ ≅ (DerivedCategory.singleFunctor D 0).obj (F.obj A) :=
    (F.mapDerivedCategorySingleFunctor 0).app A
  let e₂ : r.obj (B₀⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor C 0).obj (G.obj B))⟦(n : ℤ)⟧ :=
    (r.commShiftIso (n : ℤ)).app B₀ ≪≫
      (shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso
        ((G.mapDerivedCategorySingleFunctor 0).app B)
  exact (Ext.homAddEquiv (X := F.obj A) (Y := B) (n := n)).trans
    ((morphismAddEquiv e₁.symm (Iso.refl _)).trans
      ((e.homAddEquiv A₀ (B₀⟦(n : ℤ)⟧)).trans
        ((morphismAddEquiv (Iso.refl _) e₂).trans
          (Ext.homAddEquiv (X := A) (Y := G.obj B) (n := n)).symm)))

end

end ManuscriptAudit.ExactFunctorDerivedAdjunction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExactFunctorDerivedAdjunction.extAdjunction
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
