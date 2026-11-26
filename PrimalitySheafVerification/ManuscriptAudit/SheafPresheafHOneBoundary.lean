import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Restricting a degree-one boundary in the native cohomology presheaf

The degree-zero element from a section is obtained by the free abelian
sheaf on a representable. Restriction is precomposition by the map
of these free sheaves. Yoneda and associativity of Ext composition
identify the restricted connecting class.
-/

namespace ManuscriptAudit.SheafPresheafHOneBoundary

open CategoryTheory CategoryTheory.Abelian Opposite

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

private abbrev freePresheaf : (Cᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free

private abbrev forgetPresheaf : (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (Cᵒᵖ ⥤ Type v) :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj (forget AddCommGrpCat.{v})

abbrev freeYoneda : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ freePresheaf ⋙ presheafToSheaf J AddCommGrpCat.{v}

private def freeAdjunction :
    freePresheaf ⋙ presheafToSheaf J AddCommGrpCat.{v} ⊣
      sheafToPresheaf J AddCommGrpCat.{v} ⋙ forgetPresheaf :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J AddCommGrpCat.{v})

/-- The representing equivalence of a section on an arbitrary object of the site. -/
def sectionEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    ((freeYoneda J).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((freeAdjunction J).homEquiv (yoneda.obj U) F).trans yonedaEquiv

abbrev sectionHom (F : Sheaf J AddCommGrpCat.{v}) (U : C)
    (s : F.obj.obj (op U)) : (freeYoneda J).obj U ⟶ F :=
  (sectionEquiv J F U).symm s

theorem sectionHom_restrict (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (f : V ⟶ U)
    (s : F.obj.obj (op U)) :
    (freeYoneda J).map f ≫ sectionHom J F U s =
      sectionHom J F V (F.obj.map f.op s) := by
  change (freePresheaf ⋙ presheafToSheaf J AddCommGrpCat.{v}).map (yoneda.map f) ≫
      ((freeAdjunction J).homEquiv (yoneda.obj U) F).symm (yonedaEquiv.symm s) =
    ((freeAdjunction J).homEquiv (yoneda.obj V) F).symm (yonedaEquiv.symm (F.obj.map f.op s))
  rw [← (freeAdjunction J).homEquiv_naturality_left_symm,
    yonedaEquiv_symm_naturality_left] <;> rfl

theorem sectionHom_map {F G : Sheaf J AddCommGrpCat.{v}} (a : F ⟶ G) (U : C)
    (s : F.obj.obj (op U)) :
    sectionHom J F U s ≫ a = sectionHom J G U (a.hom.app (op U) s) := by
  change ((freeAdjunction J).homEquiv (yoneda.obj U) F).symm (yonedaEquiv.symm s) ≫ a =
    ((freeAdjunction J).homEquiv (yoneda.obj U) G).symm
      (yonedaEquiv.symm (a.hom.app (op U) s))
  rw [← (freeAdjunction J).homEquiv_naturality_right_symm,
    yonedaEquiv_symm_naturality_right] <;> rfl

/-- The connecting class of a section in the actual cohomology presheaf. -/
def boundaryOfSection (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)
    (U : C) (s : S.X₃.obj.obj (op U)) : S.X₁.H' 1 U :=
  (Ext.mk₀ (sectionHom J S.X₃ U s)).comp hS.extClass rfl

set_option backward.isDefEq.respectTransparency false in
theorem boundaryOfSection_restrict (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) {U V : C} (f : V ⟶ U) (s : S.X₃.obj.obj (op U)) :
    (S.X₁.cohomologyPresheaf 1).map f.op (boundaryOfSection J S hS U s) =
      boundaryOfSection J S hS V (S.X₃.obj.map f.op s) := by
  change (Ext.mk₀ ((freeYoneda J).map f)).comp
    ((Ext.mk₀ (sectionHom J S.X₃ U s)).comp hS.extClass rfl) rfl = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, sectionHom_restrict] <;> rfl

theorem boundaryOfSection_zero_of_lift (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) (U : C) (s : S.X₃.obj.obj (op U)) (t : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) t = s) : boundaryOfSection J S hS U s = 0 := by
  have hExact := Ext.covariant_sequence_exact₃' ((freeYoneda J).obj U) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExact
  apply (hExact (Ext.mk₀ (sectionHom J S.X₃ U s))).2
  refine ⟨Ext.mk₀ (sectionHom J S.X₂ U t), ?_⟩
  change (Ext.mk₀ (sectionHom J S.X₂ U t)).comp (Ext.mk₀ S.g) rfl =
    Ext.mk₀ (sectionHom J S.X₃ U s)
  rw [Ext.mk₀_comp_mk₀, sectionHom_map, h]


theorem boundaryOfSection_eq_zero_iff (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) (U : C) (s : S.X₃.obj.obj (op U)) :
    boundaryOfSection J S hS U s = 0 ↔
      ∃ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t = s := by
  constructor
  · intro h
    have hExact := Ext.covariant_sequence_exact₃' ((freeYoneda J).obj U) hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hExact
    obtain ⟨y, hy⟩ := (hExact (Ext.mk₀ (sectionHom J S.X₃ U s))).1 h
    obtain ⟨k, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) S.X₂).surjective y
    have hk : k ≫ S.g = sectionHom J S.X₃ U s := by
      apply (Ext.mk₀_bijective ((freeYoneda J).obj U) S.X₃).injective
      change (Ext.mk₀ k).comp (Ext.mk₀ S.g) rfl =
        Ext.mk₀ (sectionHom J S.X₃ U s) at hy
      simpa only [Ext.mk₀_comp_mk₀] using hy
    let t := sectionEquiv J S.X₂ U k
    have ht : sectionHom J S.X₂ U t = k := (sectionEquiv J S.X₂ U).symm_apply_apply k
    refine ⟨t, (sectionEquiv J S.X₃ U).symm.injective ?_⟩
    change sectionHom J S.X₃ U (S.g.hom.app (op U) t) = sectionHom J S.X₃ U s
    rw [← sectionHom_map, ht, hk]
  · rintro ⟨t, ht⟩
    exact boundaryOfSection_zero_of_lift J S hS U s t ht

end

end ManuscriptAudit.SheafPresheafHOneBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.SheafPresheafHOneBoundary.sectionHom_restrict,
      ``ManuscriptAudit.SheafPresheafHOneBoundary.sectionHom_map,
      ``ManuscriptAudit.SheafPresheafHOneBoundary.boundaryOfSection_restrict,
      ``ManuscriptAudit.SheafPresheafHOneBoundary.boundaryOfSection_zero_of_lift,
      ``ManuscriptAudit.SheafPresheafHOneBoundary.boundaryOfSection_eq_zero_iff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
