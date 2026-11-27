import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction

/-! The projections of an actual product detect degree-one Ext classes. -/

namespace ManuscriptAudit.ExtOneProduct

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w i

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
variable {I : Type i} (B : I → C) [HasProduct B] (A : C)

/-- The actual projections induce the degree-one Ext map into the product of groups. -/
def projectionMap : Ext A (∏ᶜ B) 1 →+ ∀ i, Ext A (B i) 1 where
  toFun e i := e.comp (Ext.mk₀ (Pi.π B i)) (add_zero 1)
  map_zero' := by
    funext i
    exact map_zero ((Ext.mk₀ (Pi.π B i)).postcomp A (add_zero 1))
  map_add' x y := by
    funext i
    exact map_add ((Ext.mk₀ (Pi.π B i)).postcomp A (add_zero 1)) x y

/-- A native degree-one extension class vanishes when its pushout along
every product projection vanishes. -/
theorem projectionMap_injective : Function.Injective (projectionMap B A) := by
  have zero_of_map (e : Ext A (∏ᶜ B) 1) (he : projectionMap B A e = 0) : e = 0 := by
    obtain ⟨E, j, p, w, h, rfl⟩ := ExtOneAdjunction.exists_extension e
    let S := ShortComplex.mk j p w
    have hS : S.ShortExact := h
    have hπ (i : I) : ∃ t : E ⟶ B i, j ≫ t = Pi.π B i := by
      have hi := congrArg (fun z : ∀ i, Ext A (B i) 1 ↦ z i) he
      change hS.extClass.comp (Ext.mk₀ (Pi.π B i)) (add_zero 1) = 0 at hi
      obtain ⟨e', he'⟩ :=
        Ext.contravariant_sequence_exact₁ hS (B i) (Ext.mk₀ (Pi.π B i)) rfl hi
      obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective (C := C) E (B i)).surjective e'
      refine ⟨t, (Ext.mk₀_bijective _ _).injective ?_⟩
      change (Ext.mk₀ j).comp (Ext.mk₀ t) rfl = Ext.mk₀ (Pi.π B i) at he'
      rwa [Ext.mk₀_comp_mk₀] at he'
    choose t ht using hπ
    let r := Pi.lift t
    have hr : j ≫ r = 𝟙 _ := by
      apply Pi.hom_ext
      intro i
      simpa only [r, Category.assoc, Pi.lift_π, Category.id_comp] using ht i
    have hz := hS.extClass_comp_assoc (Ext.mk₀ r) (h := rfl)
    change hS.extClass.comp ((Ext.mk₀ j).comp (Ext.mk₀ r) rfl) rfl = 0 at hz
    rw [Ext.mk₀_comp_mk₀, hr, Ext.comp_mk₀_id] at hz
    exact hz
  intro x y h
  apply sub_eq_zero.mp
  apply zero_of_map
  rw [map_sub, h, sub_self]

end
end ManuscriptAudit.ExtOneProduct

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtOneProduct.projectionMap_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
