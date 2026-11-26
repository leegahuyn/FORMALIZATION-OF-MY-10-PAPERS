import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# The derived adjunction of exact additive functors

The ordinary adjunction acts degree by degree on cochain complexes.
Exactness makes the two complex functors descend along the
quasi-isomorphism localizations, so the native localization adjunction
gives the adjunction on derived categories.
-/

namespace ManuscriptAudit.ExactFunctorDerivedAdjunction

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section Cochains

variable {C D : Type*} [Category* C] [Category* D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- An adjunction of zero-preserving functors acts on cochain complexes degree by degree. -/
def cochainAdjunction (a : F ⊣ G) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      G.mapHomologicalComplex (ComplexShape.up ℤ) where
  unit :=
    { app := fun K =>
        { f := fun n => a.unit.app (K.X n)
          comm' := fun i j _ => (a.unit.naturality (K.d i j)).symm }
      naturality := fun K L f => by
        ext n
        exact a.unit.naturality (f.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => a.counit.app (K.X n)
          comm' := fun i j _ => (a.counit.naturality (K.d i j)).symm }
      naturality := fun K L f => by
        ext n
        exact a.counit.naturality (f.f n) }
  left_triangle_components K := by
    ext n
    exact a.left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n
    exact a.right_triangle_components (K.X n)

end Cochains

section Derived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory C] [HasDerivedCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The exact left and right adjoints induce adjoint native derived functors. -/
def derivedAdjunction (a : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let L := DerivedCategory.Q (C := C)
  let R := DerivedCategory.Q (C := D)
  let c := ComplexShape.up ℤ
  let F' := F.mapDerivedCategory
  let G' := G.mapDerivedCategory
  letI : CatCommSq (F.mapHomologicalComplex c) L R F' :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex c) R L G' :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (cochainAdjunction a).localization L (HomologicalComplex.quasiIso C c)
    R (HomologicalComplex.quasiIso D c) F' G'

/-- The induced functor on the native derived categories is additive. -/
theorem mapDerivedCategory_additive : F.mapDerivedCategory.Additive := by
  rw [Localization.functor_additive_iff
    (DerivedCategory.Qh (C := C)) (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso F.mapDerivedCategoryFactorsh

end Derived

end

end ManuscriptAudit.ExactFunctorDerivedAdjunction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExactFunctorDerivedAdjunction.cochainAdjunction,
      ``ManuscriptAudit.ExactFunctorDerivedAdjunction.derivedAdjunction,
      ``ManuscriptAudit.ExactFunctorDerivedAdjunction.mapDerivedCategory_additive] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
