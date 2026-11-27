import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.Basic

/-! Degree-one injectivity for a kernel can be tested on global degree
zero without any epimorphism assumption on the original map. -/

namespace ManuscriptAudit.KernelImageHOne

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {F G : C} (g : F ⟶ G)

private theorem zero : kernel.ι g ≫ Abelian.factorThruImage g = 0 := by
  apply (cancel_mono (Abelian.image.ι g)).mp
  rw [Category.assoc, Abelian.image.fac, kernel.condition, zero_comp]

/-- The actual kernel, original domain and categorical image of one map. -/
def sequence : ShortComplex C :=
  ShortComplex.mk (kernel.ι g) (Abelian.factorThruImage g) (zero g)

private def firstIsKernel : IsLimit (KernelFork.ofι (sequence g).f (sequence g).zero) := by
  letI : Mono (sequence g).f := inferInstanceAs (Mono (kernel.ι g))
  apply KernelFork.IsLimit.ofι'
  intro X k hk
  change k ≫ Abelian.factorThruImage g = 0 at hk
  have hz : k ≫ g = 0 := by
    rw [← Abelian.image.fac g, ← Category.assoc, hk, zero_comp]
  exact ⟨kernel.lift g k hz, kernel.lift_ι _ _ _⟩

theorem sequence_shortExact : (sequence g).ShortExact :=
  ShortComplex.ShortExact.mk' ((sequence g).exact_of_f_is_kernel (firstIsKernel g))
    (inferInstanceAs (Mono (kernel.ι g))) (inferInstanceAs (Epi (Abelian.factorThruImage g)))

variable (T : C)

private theorem image_postcomp_surjective
    (h : Function.Surjective (fun a : T ⟶ F ↦ a ≫ g)) :
    Function.Surjective ((Ext.mk₀ (Abelian.factorThruImage g)).postcomp T (add_zero 0)) := by
  intro a
  let a₀ := Ext.addEquiv₀ a
  obtain ⟨b, hb⟩ := h (a₀ ≫ Abelian.image.ι g)
  have hb' : b ≫ Abelian.factorThruImage g = a₀ := by
    apply (cancel_mono (Abelian.image.ι g)).mp
    rw [Category.assoc, Abelian.image.fac]
    exact hb
  refine ⟨Ext.mk₀ b, ?_⟩
  change (Ext.mk₀ b).comp (Ext.mk₀ (Abelian.factorThruImage g)) (zero_add 0) = a
  rw [Ext.mk₀_comp_mk₀, hb']
  exact Ext.mk₀_addEquiv₀_apply a

/-- Surjectivity on actual degree zero implies injectivity of the
kernel map in actual degree one. -/
theorem one_postcomp_injective
    (h : Function.Surjective (fun a : T ⟶ F ↦ a ≫ g)) :
    Function.Injective ((Ext.mk₀ (kernel.ι g)).postcomp T (add_zero 1)) := by
  let hS := sequence_shortExact g
  let d := (Ext.mk₀ (kernel.ι g)).postcomp T (add_zero 1)
  have he := Ext.covariant_sequence_exact₃' T hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  have hδ (a : Ext T (Abelian.image g) 0) : a.comp hS.extClass (show 0 + 1 = 1 by rfl) = 0 :=
    (he a).mpr (image_postcomp_surjective g T h a)
  intro a b hab
  apply sub_eq_zero.mp
  have hz : d (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ T hS (a - b) hz
    (show 0 + 1 = 1 by rfl)
  exact hc.symm.trans (hδ c)

end

end ManuscriptAudit.KernelImageHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KernelImageHOne.sequence_shortExact,
      ``ManuscriptAudit.KernelImageHOne.one_postcomp_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
