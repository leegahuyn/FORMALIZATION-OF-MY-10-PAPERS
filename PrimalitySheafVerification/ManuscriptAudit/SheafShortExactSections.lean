import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# A short exact sequence and sheaf cohomology

Vanishing H¹ of the first sheaf gives surjective terminal sections.
Vanishing H¹ of the quotient gives an injection in degree two.
-/

namespace ManuscriptAudit.SheafShortExactSections

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)

include hS

private noncomputable abbrev Z :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- Evaluation preserves exactness at the middle of a short exact sequence. -/
theorem sections_exact (W : C) :
    Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op W)
  have hK := (KernelFork.ofι S.f S.zero).mapIsLimit hS.fIsKernel E
  have h := ShortComplex.exact_of_f_is_kernel (S.map E) hK
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- If the kernel has zero H¹, the quotient map is surjective on terminal sections. -/
theorem sections_surjective_of_HOne {T : C} (hT : IsTerminal T)
    (hVanishing : Subsingleton (Sheaf.H S.X₁ 1)) :
    Function.Surjective (S.g.hom.app (op T)) := by
  intro x
  let x₀ : Sheaf.H S.X₃ 0 := (Sheaf.H.equiv₀ S.X₃ hT).symm x
  have hZero : (hS.extClass.postcomp (Z (J := J)) (show 0 + 1 = 1 by rfl)) x₀ = 0 :=
    hVanishing.allEq _ _
  have hExact := Ext.covariant_sequence_exact₃' (Z (J := J)) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExact
  obtain ⟨y, hy⟩ := (hExact x₀).mp hZero
  refine ⟨Sheaf.H.equiv₀ S.X₂ hT y, ?_⟩
  change Sheaf.H.map S.g 0 y = x₀ at hy
  rw [Sheaf.H.equiv₀_naturality, hy]
  exact (Sheaf.H.equiv₀ S.X₃ hT).apply_symm_apply x

/-- If the quotient has zero H¹, the inclusion is injective on H². -/
theorem HTwo_map_injective_of_HOne (hVanishing : Subsingleton (Sheaf.H S.X₃ 1)) :
    Function.Injective (Sheaf.H.map S.f 2) := by
  intro x y hxy
  have hx : Sheaf.H.map S.f 2 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  change (x - y).comp (Ext.mk₀ S.f) (add_zero 2) = 0 at hx
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (Z (J := J)) hS (x - y) hx
    (show 1 + 1 = 2 by rfl)
  have hz' : z = 0 := hVanishing.allEq _ _
  apply sub_eq_zero.mp
  rw [← hz, hz', Ext.zero_comp]

end ManuscriptAudit.SheafShortExactSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafShortExactSections.sections_exact,
      ``ManuscriptAudit.SheafShortExactSections.sections_surjective_of_HOne,
      ``ManuscriptAudit.SheafShortExactSections.HTwo_map_injective_of_HOne] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
