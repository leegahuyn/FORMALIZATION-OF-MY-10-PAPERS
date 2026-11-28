import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! Composition and naturality of the exact-functor map on Ext in
degree one, proved on the genuine connecting classes. -/

namespace ManuscriptAudit.ExtOneFunctoriality

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w' u'' v'' w''
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private abbrev seq {Y : C} := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
  (cokernel.condition (Injective.ι Y))

private theorem seq_short {Y : C} : (seq (Y := Y)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι Y))
  mono_f := inferInstanceAs (Mono (Injective.ι Y))
  epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι Y)))

private theorem rep {X Y : C} (a : Ext X Y 1) :
    ∃ p : X ⟶ cokernel (Injective.ι Y),
      (Ext.mk₀ p).comp (seq_short (Y := Y)).extClass (zero_add 1) = a := by
  let m := Injective.ι Y
  have hz : a.comp (Ext.mk₀ m) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  have h := Ext.covariant_sequence_exact₁' X (seq_short (Y := Y)) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz'⟩ := (h a).1 hz
  obtain ⟨p, rfl⟩ := (Ext.mk₀_bijective X (cokernel m)).surjective z
  exact ⟨p, hz'⟩

variable (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The genuine exact-functor map in degree one respects actual composition. -/
theorem map_comp_functor {X Y : C} (a : Ext X Y 1) :
    (a.mapExactFunctor F).mapExactFunctor G = a.mapExactFunctor (F ⋙ G) := by
  obtain ⟨p, rfl⟩ := rep a
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass] <;> rfl

variable {F} (F' : C ⥤ D) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

/-- An actual natural map of exact functors intertwines their Ext¹ maps
by the true maps on both arguments of Ext. -/
theorem map_natural (η : F ⟶ F') {X Y : C} (a : Ext X Y 1) :
    (a.mapExactFunctor F).comp (Ext.mk₀ (η.app Y)) (add_zero 1) =
      (Ext.mk₀ (η.app X)).comp (a.mapExactFunctor F') (zero_add 1) := by
  obtain ⟨p, rfl⟩ := rep a
  let S := seq (Y := Y)
  let h := seq_short (Y := Y)
  let L := h.map_of_exact F
  let R := h.map_of_exact F'
  let c : S.map F ⟶ S.map F' :=
    { τ₁ := η.app S.X₁, τ₂ := η.app S.X₂, τ₃ := η.app S.X₃,
      comm₁₂ := (η.naturality S.f).symm, comm₂₃ := (η.naturality S.g).symm }
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  change ((Ext.mk₀ (F.map p)).comp L.extClass (zero_add 1)).comp
      (Ext.mk₀ (η.app Y)) (add_zero 1) =
    (Ext.mk₀ (η.app X)).comp ((Ext.mk₀ (F'.map p)).comp R.extClass (zero_add 1)) (zero_add 1)
  calc
    _ = (Ext.mk₀ (F.map p)).comp (L.extClass.comp (Ext.mk₀ (η.app Y)) (add_zero 1)) (zero_add 1) :=
      Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = (Ext.mk₀ (F.map p)).comp ((Ext.mk₀ (η.app S.X₃)).comp R.extClass (zero_add 1)) (zero_add 1) :=
      congrArg (fun z => (Ext.mk₀ (F.map p)).comp z (zero_add 1)) (L.extClass_naturality R c)
    _ = (Ext.mk₀ (F.map p ≫ η.app S.X₃)).comp R.extClass (zero_add 1) :=
      Ext.mk₀_comp_mk₀_assoc _ _ _
    _ = (Ext.mk₀ (η.app X ≫ F'.map p)).comp R.extClass (zero_add 1) :=
      congrArg (fun f => (Ext.mk₀ f).comp R.extClass (zero_add 1)) (η.naturality p)
    _ = _ := (Ext.mk₀_comp_mk₀_assoc _ _ _).symm

end

end ManuscriptAudit.ExtOneFunctoriality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExtOneFunctoriality.map_comp_functor,
      ``ManuscriptAudit.ExtOneFunctoriality.map_natural] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
