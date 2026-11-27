import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorExtAdjunction

/-! The actual Ext adjunction is natural in its coefficient argument. -/

namespace ManuscriptAudit.ExactFunctorExtAdjunctionNaturality

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ExactFunctorDerivedAdjunction (extAdjunction derivedAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasExt C] [HasExt D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

attribute [local instance] HasDerivedCategory.standard

private abbrev single (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C] :=
  DerivedCategory.singleFunctor C 0

private abbrev shift (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C] (n : ℕ) :=
  shiftFunctor (DerivedCategory C) (n : ℤ)

private abbrev leftComparison (A : C) :=
  (F.mapDerivedCategorySingleFunctor 0).app A

private abbrev rightComparison (B : D) (n : ℕ) :=
  (G.mapDerivedCategory.commShiftIso (n : ℤ)).app ((single D).obj B) ≪≫
    (shift C n).mapIso ((G.mapDerivedCategorySingleFunctor 0).app B)

private theorem rightComparison_naturality {B B' : D} (f : B ⟶ B') (n : ℕ) :
    G.mapDerivedCategory.map ((shift D n).map ((single D).map f)) ≫
        (rightComparison (G := G) B' n).hom =
      (rightComparison (G := G) B n).hom ≫ (shift C n).map ((single C).map (G.map f)) := by
  let R := G.mapDerivedCategory
  let i := (R.commShiftIso (n : ℤ)).hom
  let j := (G.mapDerivedCategorySingleFunctor 0).hom
  let u := (single D).map f
  have hi : R.map ((shift D n).map u) ≫ i.app ((single D).obj B') =
      i.app ((single D).obj B) ≫ (shift C n).map (R.map u) := i.naturality u
  have hj : R.map u ≫ j.app B' = j.app B ≫ (single C).map (G.map f) := j.naturality f
  change R.map ((shift D n).map u) ≫
      (i.app ((single D).obj B') ≫ (shift C n).map (j.app B')) =
    (i.app ((single D).obj B) ≫ (shift C n).map (j.app B)) ≫
      (shift C n).map ((single C).map (G.map f))
  calc
    _ = (i.app ((single D).obj B) ≫ (shift C n).map (R.map u)) ≫
        (shift C n).map (j.app B') := by rw [← Category.assoc, hi]
    _ = i.app ((single D).obj B) ≫ (shift C n).map (R.map u ≫ j.app B') := by
      rw [Category.assoc, Functor.map_comp]
    _ = _ := by rw [hj, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1600000 in
private theorem extAdjunction_hom (a : F ⊣ G) (A : C) (B : D) (n : ℕ)
    (x : Ext (F.obj A) B n) :
    (extAdjunction a A B n x).hom =
      ((derivedAdjunction a).homEquiv ((single C).obj A) (((single D).obj B)⟦(n : ℤ)⟧))
        ((leftComparison (F := F) A).hom ≫ x.hom) ≫
          (rightComparison (G := G) B n).hom := by
  let adj := (derivedAdjunction a).homEquiv ((single C).obj A) (((single D).obj B)⟦(n : ℤ)⟧)
  let e := (leftComparison (F := F) A).hom
  let i := (rightComparison (G := G) B n).hom
  change Ext.homEquiv (Ext.homEquiv.symm ((𝟙 _ ≫ adj (e ≫ x.hom ≫ 𝟙 _)) ≫ i)) =
    adj (e ≫ x.hom) ≫ i
  rw [Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 1600000 in
/-- Actual composition on the second argument commutes with the derived Ext adjunction. -/
theorem naturality (a : F ⊣ G) (A : C) {B B' : D} (f : B ⟶ B') (n : ℕ)
    (x : Ext (F.obj A) B n) :
    extAdjunction a A B' n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (extAdjunction a A B n x).comp (Ext.mk₀ (G.map f)) (add_zero n) := by
  apply Ext.homEquiv.injective
  change (extAdjunction a A B' n (x.comp (Ext.mk₀ f) (add_zero n))).hom =
    ((extAdjunction a A B n x).comp (Ext.mk₀ (G.map f)) (add_zero n)).hom
  simp only [extAdjunction_hom, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  rw [← Category.assoc (leftComparison (F := F) A).hom,
    (derivedAdjunction a).homEquiv_naturality_right, Category.assoc,
    rightComparison_naturality, ← Category.assoc]

end
end ManuscriptAudit.ExactFunctorExtAdjunctionNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExactFunctorExtAdjunctionNaturality.naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
