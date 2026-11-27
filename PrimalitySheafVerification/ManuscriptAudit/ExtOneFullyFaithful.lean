import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction

/-! An exact fully faithful functor detects degree-one extensions. -/

namespace ManuscriptAudit.ExtOneFullyFaithful

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The native Ext¹ map of an exact fully faithful functor is injective. -/
theorem map_injective (X Y : C) : Function.Injective (F.mapExtAddHom X Y 1) := by
  have zero_of_map (e : Ext X Y 1) (he : F.mapExtAddHom X Y 1 e = 0) : e = 0 := by
    obtain ⟨E, j, p, w, hs, rfl⟩ := ExtOneAdjunction.exists_extension e
    let S := ShortComplex.mk j p w
    have hS : S.ShortExact := hs
    change hS.extClass.mapExactFunctor F = 0 at he
    rw [Ext.mapExactFunctor_extClass] at he
    let T := S.map F
    let hT : T.ShortExact := hS.map_of_exact F
    have hz : hT.extClass.comp (Ext.mk₀ (𝟙 T.X₁)) (add_zero 1) = 0 :=
      (Ext.comp_mk₀_id hT.extClass).trans he
    obtain ⟨e', he'⟩ := Ext.contravariant_sequence_exact₁ hT T.X₁
      (Ext.mk₀ (𝟙 T.X₁)) rfl hz
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).surjective e'
    have ht : F.map j ≫ t = 𝟙 (F.obj Y) := by
      apply (Ext.mk₀_bijective _ _).injective
      change (Ext.mk₀ (F.map j)).comp (Ext.mk₀ t) rfl = Ext.mk₀ (𝟙 (F.obj Y)) at he'
      rwa [Ext.mk₀_comp_mk₀] at he'
    let q := F.preimage t
    have hq : j ≫ q = 𝟙 Y := by
      apply F.map_injective
      calc
        F.map (j ≫ q) = F.map j ≫ F.map q := F.map_comp j q
        _ = F.map j ≫ t := congrArg (fun f ↦ F.map j ≫ f) (F.map_preimage t)
        _ = 𝟙 (F.obj Y) := ht
        _ = F.map (𝟙 Y) := (F.map_id Y).symm
    have h := hS.extClass_comp_assoc (Ext.mk₀ q) (h := rfl)
    change hS.extClass.comp ((Ext.mk₀ j).comp (Ext.mk₀ q) rfl) rfl = 0 at h
    rw [Ext.mk₀_comp_mk₀, hq, Ext.comp_mk₀_id] at h
    exact h
  intro a b hab
  apply sub_eq_zero.mp
  apply zero_of_map
  rw [map_sub, hab, sub_self]

end
end ManuscriptAudit.ExtOneFullyFaithful

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtOneFullyFaithful.map_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
