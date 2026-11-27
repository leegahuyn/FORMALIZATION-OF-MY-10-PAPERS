import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Abelian.Basic

/-! In degree one, an exact left adjoint induces an injection into Ext
after composing with its counit. This is the low-degree derived
comparison needed for direct image, without assuming exact direct image. -/

namespace ManuscriptAudit.ExtOneAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- Every degree-one class is represented by a native short exact extension. -/
theorem exists_extension {X Y : C} (e : Ext X Y 1) :
    ∃ (E : C) (j : Y ⟶ E) (p : E ⟶ X) (w : j ≫ p = 0)
      (h : (ShortComplex.mk j p w).ShortExact), h.extClass = e := by
  let I : InjectivePresentation Y := Classical.arbitrary _
  haveI : Injective I.J := I.injective
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ X hS e (Ext.eq_zero_of_injective _) rfl
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X S.X₃).surjective x
  let E := pullback S.g a
  let p := pullback.snd S.g a
  let j : Y ⟶ E := pullback.lift S.f 0 (by rw [S.zero, zero_comp])
  have hj : j ≫ pullback.fst S.g a = S.f := by simp [j]
  have hp : j ≫ p = 0 := by simp [j, p]
  haveI : Mono S.f := hS.mono_f
  haveI : Mono j := mono_of_mono_fac hj
  haveI : Epi S.g := hS.epi_g
  let T := ShortComplex.mk j p hp
  have hT : T.ShortExact := by
    refine { exact := T.exact_of_f_is_kernel ?_ }
    refine KernelFork.IsLimit.ofι' j hp (fun k hk => ?_)
    have hk' : (k ≫ pullback.fst S.g a) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (k ≫ p) ≫ a = 0
      rw [hk, zero_comp]
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.fIsKernel _ hk'
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hj]
      exact hl
    · change (l ≫ j) ≫ p = k ≫ p
      rw [Category.assoc, hp, hk, comp_zero]
  let q : T ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := pullback.fst S.g a
      τ₃ := a
      comm₁₂ := by
        change 𝟙 _ ≫ S.f = j ≫ pullback.fst S.g a
        rw [Category.id_comp, hj]
      comm₂₃ := pullback.condition }
  refine ⟨E, j, p, hp, hT, ?_⟩
  have h := hT.extClass_naturality hS q
  change hT.extClass.comp (Ext.mk₀ (𝟙 Y)) rfl =
    (Ext.mk₀ a).comp hS.extClass rfl at h
  rw [Ext.comp_mk₀_id, hx] at h
  exact h

variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Native Ext¹ map induced by an exact left adjoint followed by the counit. -/
def map (adj : F ⊣ G) (X : C) (Y : D) :
    Ext X (G.obj Y) 1 →+ Ext (F.obj X) Y 1 :=
  ((Ext.mk₀ (adj.counit.app Y)).postcomp (F.obj X) rfl).comp
    (F.mapExtAddHom X (G.obj Y) 1)

/-- The native degree-one comparison with the right adjoint is injective. -/
theorem map_injective (adj : F ⊣ G) (X : C) (Y : D) :
    Function.Injective (map adj X Y) := by
  have zero_of_map (e : Ext X (G.obj Y) 1) (he : map adj X Y e = 0) : e = 0 := by
    obtain ⟨E, j, p, w, hs, rfl⟩ := exists_extension e
    let S := ShortComplex.mk j p w
    have hS : S.ShortExact := hs
    change (hS.extClass.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app Y)) rfl = 0 at he
    rw [Ext.mapExactFunctor_extClass] at he
    obtain ⟨e', he'⟩ := Ext.contravariant_sequence_exact₁ (hS.map_of_exact F) Y
      (Ext.mk₀ (adj.counit.app Y)) rfl he
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective (F.obj E) Y).surjective e'
    have ht : F.map j ≫ t = adj.counit.app Y := by
      apply (Ext.mk₀_bijective _ _).injective
      change (Ext.mk₀ (F.map j)).comp (Ext.mk₀ t) rfl =
        Ext.mk₀ (adj.counit.app Y) at he'
      rwa [Ext.mk₀_comp_mk₀] at he'
    let r := (adj.homEquiv E Y) t
    have hr : j ≫ r = 𝟙 _ := by
      rw [← adj.homEquiv_naturality_left j t, ht, ← adj.homEquiv_symm_id Y,
        Equiv.apply_symm_apply]
    have hz := hS.extClass_comp_assoc (Ext.mk₀ r) (h := rfl)
    change hS.extClass.comp ((Ext.mk₀ j).comp (Ext.mk₀ r) rfl) rfl = 0 at hz
    rw [Ext.mk₀_comp_mk₀, hr, Ext.comp_mk₀_id] at hz
    exact hz
  intro a b hab
  apply sub_eq_zero.mp
  apply zero_of_map
  rw [map_sub, hab, sub_self]

end
end ManuscriptAudit.ExtOneAdjunction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtOneAdjunction.map_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
