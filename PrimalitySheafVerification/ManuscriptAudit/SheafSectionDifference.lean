import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Differences of local lifts in an abelian sheaf

Evaluation at a site object preserves the kernel of the sheaf cokernel
projection. Two sections with the same cokernel image then have a unique
difference in the given subsheaf. These differences satisfy the triangle
identity and commute with restriction.
-/

namespace ManuscriptAudit.SheafSectionDifference

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) [Mono i]

private abbrev evaluate (W : C) : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op W)

private abbrev sectionInclusion (W : C) : F.obj.obj (op W) ⟶ I.obj.obj (op W) :=
  i.hom.app (op W)

private noncomputable abbrev sectionProjection (W : C) :
    I.obj.obj (op W) ⟶ (cokernel i).obj.obj (op W) :=
  (cokernel.π i).hom.app (op W)

/-- Evaluation of a mono and its sheaf cokernel is exact in the middle. -/
theorem cokernel_sections_exact (W : C) :
    Function.Exact (i.hom.app (op W)) ((cokernel.π i).hom.app (op W)) := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.Exact := Abelian.exact_cokernel i
  letI : Mono S.f := inferInstanceAs (Mono i)
  have hK := (KernelFork.ofι S.f S.zero).mapIsLimit hS.fIsKernel (evaluate (J := J) W)
  have h := ShortComplex.exact_of_f_is_kernel (S.map (evaluate (J := J) W)) hK
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Evaluating a sheaf monomorphism gives an injective map on sections. -/
theorem section_injective (W : C) : Function.Injective (i.hom.app (op W)) := by
  have h : Mono ((evaluate (J := J) W).map i) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp h

/-- Every difference of two lifts is represented by a unique subsheaf section. -/
theorem existsUnique_difference (W : C) (a b : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b) :
    ∃! d : F.obj.obj (op W), sectionInclusion i W d = a - b := by
  have hzero : sectionProjection i W (a - b) = 0 := by
    change (sectionProjection i W).hom (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨d, hd⟩ := (cokernel_sections_exact i W (a - b)).1 hzero
  refine ⟨d, hd, fun y hy => ?_⟩
  exact section_injective i W (hy.trans hd.symm)

/-- The unique subsheaf section representing the difference of two lifts. -/
noncomputable def difference (W : C) (a b : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b) : F.obj.obj (op W) :=
  (existsUnique_difference i W a b hab).exists.choose

theorem difference_spec (W : C) (a b : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b) :
    sectionInclusion i W (difference i W a b hab) = a - b :=
  (existsUnique_difference i W a b hab).exists.choose_spec

/-- Differences of three lifts satisfy the additive cocycle identity. -/
theorem difference_add (W : C) (a b c : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b)
    (hbc : sectionProjection i W b = sectionProjection i W c) :
    difference i W a b hab + difference i W b c hbc =
      difference i W a c (hab.trans hbc) := by
  apply section_injective i W
  change (sectionInclusion i W).hom (_ + _) = (sectionInclusion i W).hom _
  rw [map_add]
  change sectionInclusion i W (difference i W a b hab) +
    sectionInclusion i W (difference i W b c hbc) =
      sectionInclusion i W (difference i W a c (hab.trans hbc))
  rw [difference_spec, difference_spec, difference_spec, sub_add_sub_cancel]

/-- Two equal-image sections retain equal image when restricted. -/
theorem same_image_of_restriction {V W : C} (r : V ⟶ W) (a b : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b) :
    sectionProjection i V (I.obj.map r.op a) = sectionProjection i V (I.obj.map r.op b) := by
  have h (x : I.obj.obj (op W)) :
      sectionProjection i V (I.obj.map r.op x) =
        (cokernel i).obj.map r.op (sectionProjection i W x) :=
    ConcreteCategory.congr_hom ((cokernel.π i).hom.naturality r.op) x
  rw [h a, h b, hab]

/-- The difference of two lifts restricts to the difference of their restrictions. -/
theorem difference_restrict {V W : C} (r : V ⟶ W) (a b : I.obj.obj (op W))
    (hab : sectionProjection i W a = sectionProjection i W b) :
    F.obj.map r.op (difference i W a b hab) =
      difference i V (I.obj.map r.op a) (I.obj.map r.op b)
        (same_image_of_restriction i r a b hab) := by
  apply section_injective i V
  have h (x : F.obj.obj (op W)) :
      sectionInclusion i V (F.obj.map r.op x) = I.obj.map r.op (sectionInclusion i W x) :=
    ConcreteCategory.congr_hom (i.hom.naturality r.op) x
  rw [h, difference_spec, difference_spec]
  change (I.obj.map r.op).hom (a - b) =
    (I.obj.map r.op).hom a - (I.obj.map r.op).hom b
  exact map_sub _ _ _

end ManuscriptAudit.SheafSectionDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafSectionDifference.cokernel_sections_exact,
      ``ManuscriptAudit.SheafSectionDifference.section_injective,
      ``ManuscriptAudit.SheafSectionDifference.existsUnique_difference,
      ``ManuscriptAudit.SheafSectionDifference.difference_spec,
      ``ManuscriptAudit.SheafSectionDifference.difference_add,
      ``ManuscriptAudit.SheafSectionDifference.same_image_of_restriction,
      ``ManuscriptAudit.SheafSectionDifference.difference_restrict] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
