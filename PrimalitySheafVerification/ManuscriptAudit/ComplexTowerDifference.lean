import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! The actual product difference and mapping cocone of a countable tower of cochain complexes. -/

namespace ManuscriptAudit.ComplexTowerDifference

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u w z

set_option backward.isDefEq.respectTransparency false

section Category

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : ℕ → C) (transition : ∀ r, K (r + 1) ⟶ K r) [HasProduct K]

/-- Identity minus the shift induced by the consecutive arrows of the tower. -/
def difference : (∏ᶜ K) ⟶ (∏ᶜ K) :=
  𝟙 (∏ᶜ K) - Pi.map' Nat.succ transition

@[reassoc]
theorem difference_π (r : ℕ) :
    difference K transition ≫ Pi.π K r =
      Pi.π K r - Pi.π K (r + 1) ≫ transition r := by
  simp only [difference, Preadditive.sub_comp, Category.id_comp, Pi.map'_comp_π]

variable {D : Type w} [Category.{z} D] [Preadditive D]
variable (F : C ⥤ D) [F.Additive] [HasProduct (fun r ↦ F.obj (K r))]

/-- The canonical product comparison intertwines the product differences. -/
theorem map_difference_comp_comparison :
    F.map (difference K transition) ≫ piComparison F K =
      piComparison F K ≫ difference (fun r ↦ F.obj (K r)) (fun r ↦ F.map (transition r)) := by
  apply Pi.hom_ext
  intro r
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, difference_π,
    F.map_sub, F.map_comp, Category.assoc, difference_π, Preadditive.comp_sub,
    piComparison_comp_π, ← Category.assoc, piComparison_comp_π]

end Category

section Complex

private abbrev A := AddCommGrpCat.{0}
private abbrev Ch := CochainComplex A ℤ

variable (K : ℕ → Ch) (transition : ∀ r, K (r + 1) ⟶ K r)

/-- The actual mapping cocone of the product difference for a countable tower. -/
def mappingFiber : Ch :=
  CochainComplex.mappingCocone (difference K transition)

/-- The homotopy-fibre comparison is the native first projection of the mapping cocone. -/
def toProduct : mappingFiber K transition ⟶ ∏ᶜ K :=
  CochainComplex.mappingCocone.fst (difference K transition)

/-- The projection and the difference are the first two arrows of the natural cone triangle. -/
def triangle : Triangle Ch :=
  CochainComplex.mappingCocone.triangle (difference K transition)

theorem triangle_mor₁ :
    (triangle K transition).mor₁ = toProduct K transition := rfl

theorem triangle_mor₂ :
    (triangle K transition).mor₂ = difference K transition := rfl

/-- The product-difference cone triangle is distinguished in the actual derived category. -/
theorem triangle_distinguished [HasDerivedCategory A] :
    (DerivedCategory.Q (C := A)).mapTriangle.obj (triangle K transition) ∈
      distTriang (DerivedCategory A) :=
  DerivedCategory.mappingCocone_triangle_distinguished (difference K transition)

/-- The natural short segment after taking homology of the mapping cocone and the product. -/
theorem homology_exact [HasDerivedCategory A] (n : ℤ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (toProduct K transition) n)
      (HomologicalComplex.homologyMap (difference K transition) n)
      (CochainComplex.homologyMap_comp_eq_zero_of_distTriang
        (triangle K transition) (triangle_distinguished K transition) n)).Exact :=
  CochainComplex.homologyMap_exact₂_of_distTriang
    (triangle K transition) (triangle_distinguished K transition) n

/-- Before using product exactness, the canonical homology comparison already
intertwines the actual difference with the difference on finite-level homology. -/
theorem homology_difference (n : ℤ) :
    let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n
    H.map (difference K transition) ≫ piComparison H K =
      piComparison H K ≫ difference (fun r ↦ H.obj (K r)) (fun r ↦ H.map (transition r)) :=
  map_difference_comp_comparison K transition (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)

end Complex

end
end ManuscriptAudit.ComplexTowerDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ComplexTowerDifference.difference_π,
      ``ManuscriptAudit.ComplexTowerDifference.map_difference_comp_comparison,
      ``ManuscriptAudit.ComplexTowerDifference.mappingFiber,
      ``ManuscriptAudit.ComplexTowerDifference.triangle_mor₁,
      ``ManuscriptAudit.ComplexTowerDifference.triangle_mor₂,
      ``ManuscriptAudit.ComplexTowerDifference.triangle_distinguished,
      ``ManuscriptAudit.ComplexTowerDifference.homology_exact,
      ``ManuscriptAudit.ComplexTowerDifference.homology_difference] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
