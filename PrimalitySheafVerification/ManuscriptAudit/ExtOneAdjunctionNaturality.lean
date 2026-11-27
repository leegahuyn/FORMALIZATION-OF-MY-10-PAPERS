import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction

/-! The actual Ext¹ map induced by an exact adjunction commutes with
postcomposition in the coefficient object. -/

namespace ManuscriptAudit.ExtOneAdjunctionNaturality

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt C] [HasExt D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (a : F ⊣ G) (X : C) {Y Z : D} (f : Y ⟶ Z)

/-- Postcomposition commutes with the actual comparison from an exact left adjoint and its counit. -/
theorem map_postcomp (x : Ext X (G.obj Y) 1) :
    ExtOneAdjunction.map a X Z (x.comp (Ext.mk₀ (G.map f)) (add_zero 1)) =
      (ExtOneAdjunction.map a X Y x).comp (Ext.mk₀ f) (add_zero 1) := by
  have h : F.map (G.map f) ≫ a.counit.app Z = a.counit.app Y ≫ f :=
    a.counit.naturality f
  change ((x.comp (Ext.mk₀ (G.map f)) (add_zero 1)).mapExactFunctor F).comp
      (Ext.mk₀ (a.counit.app Z)) (add_zero 1) =
    ((x.mapExactFunctor F).comp (Ext.mk₀ (a.counit.app Y)) (add_zero 1)).comp
      (Ext.mk₀ f) (add_zero 1)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, h]

end
end ManuscriptAudit.ExtOneAdjunctionNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtOneAdjunctionNaturality.map_postcomp
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
