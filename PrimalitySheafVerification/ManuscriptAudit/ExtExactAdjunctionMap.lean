import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction

/-! The Ext comparison of exact adjoints commutes with the literal
coefficient maps and connecting maps in every degree. -/

namespace ManuscriptAudit.ExtExactAdjunctionMap

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

variable {F : C ⥤ D} {G : D ⥤ C}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (adj : F ⊣ G) (X : C)

/-- The actual comparison is the exact left functor followed by the counit. -/
def map (Y : D) (n : ℕ) : Ext X (G.obj Y) n →+ Ext (F.obj X) Y n :=
  ((Ext.mk₀ (adj.counit.app Y)).postcomp (F.obj X) (add_zero n)).comp
    (F.mapExtAddHom X (G.obj Y) n)

theorem map_zero_degree (Y : D) : Function.Bijective (map adj X Y 0) := by
  let a := Ext.mk₀_bijective X (G.obj Y)
  let b := Ext.mk₀_bijective (F.obj X) Y
  have h (f : X ⟶ G.obj Y) : map adj X Y 0 (Ext.mk₀ f) =
      Ext.mk₀ ((adj.homEquiv X Y).symm f) := by
    change ((Ext.mk₀ f).mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero 0) = _
    rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_counit]
  constructor
  · intro y z he
    obtain ⟨f, rfl⟩ := a.surjective y
    obtain ⟨g, rfl⟩ := a.surjective z
    rw [h, h] at he
    exact congrArg Ext.mk₀ ((adj.homEquiv X Y).symm.injective (b.injective he))
  · intro y
    obtain ⟨f, rfl⟩ := b.surjective y
    exact ⟨Ext.mk₀ (adj.homEquiv X Y f), (h _).trans
      (congrArg Ext.mk₀ ((adj.homEquiv X Y).symm_apply_apply f))⟩

theorem map_naturality {U V : D} (f : U ⟶ V) (n : ℕ) (x : Ext X (G.obj U) n) :
    map adj X V n (x.comp (Ext.mk₀ (G.map f)) (add_zero n)) =
      (map adj X U n x).comp (Ext.mk₀ f) (add_zero n) := by
  change ((x.comp (Ext.mk₀ (G.map f)) (add_zero n)).mapExactFunctor F).comp
      (Ext.mk₀ (adj.counit.app V)) (add_zero n) =
    ((x.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app U)) (add_zero n)).comp
      (Ext.mk₀ f) (add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have h : F.map (G.map f) ≫ adj.counit.app V = adj.counit.app U ≫ f :=
    adj.counit.naturality f
  rw [h]

variable [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

set_option maxHeartbeats 4800000 in
/-- The counit comparison sends the actual connecting map to the actual boundary. -/
theorem map_boundary {S : ShortComplex D} (hS : S.ShortExact) (n : ℕ)
    (x : Ext X (G.obj S.X₃) n) :
    map adj X S.X₁ (n + 1) (x.comp (hS.map_of_exact G).extClass rfl) =
      (map adj X S.X₃ n x).comp hS.extClass rfl := by
  let T := (S.map G).map F
  let hT := (hS.map_of_exact G).map_of_exact F
  let m : T ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have h := hT.extClass_naturality hS m
  change hT.extClass.comp (Ext.mk₀ (adj.counit.app S.X₁)) rfl =
    (Ext.mk₀ (adj.counit.app S.X₃)).comp hS.extClass rfl at h
  change ((x.comp (hS.map_of_exact G).extClass rfl).mapExactFunctor F).comp
      (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero (n+1)) =
    ((x.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app S.X₃)) (add_zero n)).comp
      hS.extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc, Ext.comp_assoc, h] <;> simp

end
end ManuscriptAudit.ExtExactAdjunctionMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExtExactAdjunctionMap.map_zero_degree,
      ``ManuscriptAudit.ExtExactAdjunctionMap.map_naturality,
      ``ManuscriptAudit.ExtExactAdjunctionMap.map_boundary] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
