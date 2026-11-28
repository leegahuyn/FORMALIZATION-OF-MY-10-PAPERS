import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.ExtExactAdjunctionMap

/-! The actual Ext comparison for an adjunction of exact functors
is bijective, by injective dimension shifting along its real boundaries. -/

namespace ManuscriptAudit.ExtExactAdjunctionBijective

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ExtExactAdjunctionMap (map map_zero_degree map_naturality map_boundary)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D] [EnoughInjectives D]

variable {F : C ⥤ D} {G : D ⥤ C}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G) (X : C)

set_option maxHeartbeats 7900000 in
/-- Exact direct image with its exact left adjoint computes actual Ext in every degree. -/
theorem bijective (n : ℕ) (Y : D) : Function.Bijective (map adj X Y n) := by
  letI : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing Y with
  | zero => exact map_zero_degree adj X Y
  | succ n ih =>
    let i := Injective.ι Y
    let S := ShortComplex.cokernelSequence i
    letI : Mono S.f := inferInstanceAs (Mono i)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) inferInstance inferInstance
    let T := S.map G
    let hT := hS.map_of_exact G
    letI : Injective S.X₂ := by dsimp [S, i]; infer_instance
    letI : Injective T.X₂ := G.injective_obj S.X₂
    constructor
    · have hZero (x : Ext X (G.obj Y) (n+1)) (hx : map adj X Y (n+1) x = 0) : x = 0 := by
        obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hT x (Ext.eq_zero_of_injective _) rfl
        have he : (map adj X S.X₃ n z).comp hS.extClass rfl = 0 := by
          rw [← map_boundary adj X hS n z, hz]
          exact hx
        obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ (F.obj X) hS (map adj X S.X₃ n z) rfl he
        obtain ⟨w', hw'⟩ := (ih S.X₂).surjective w
        have hEq : w'.comp (Ext.mk₀ T.g) (add_zero n) = z := by
          apply (ih S.X₃).injective
          change map adj X S.X₃ n (w'.comp (Ext.mk₀ (G.map S.g)) (add_zero n)) =
            map adj X S.X₃ n z
          rw [map_naturality, hw', hw]
        rw [← hz, ← hEq, Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
      intro a b hab
      apply sub_eq_zero.mp
      apply hZero
      rw [map_sub, hab, sub_self]
    · intro x
      obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (F.obj X) hS x (Ext.eq_zero_of_injective _) rfl
      obtain ⟨w, hw⟩ := (ih S.X₃).surjective z
      refine ⟨w.comp hT.extClass rfl, ?_⟩
      calc
        _ = (map adj X S.X₃ n w).comp hS.extClass rfl := map_boundary adj X hS n w
        _ = _ := (congrArg (fun u ↦ u.comp hS.extClass (show n + 1 = n + 1 from rfl)) hw).trans hz

end
end ManuscriptAudit.ExtExactAdjunctionBijective

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtExactAdjunctionBijective.bijective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
