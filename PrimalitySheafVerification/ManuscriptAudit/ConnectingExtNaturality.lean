import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! Naturality of the genuine derived degree-one connecting class under
an exact restriction functor, comparison of short exact sequences, and
the comparison of objects representing sections. -/

namespace ManuscriptAudit.ConnectingExtNaturality

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Derived pullback of a connecting section is the connecting section of
the restricted short exact sequence, with both comparison morphisms. -/
theorem map_connecting {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map R ⟶ T)
    {Z : C} {Z' : D} (z : Z' ⟶ R.obj Z) (x : Z ⟶ S.X₃) :
    (Ext.mk₀ z).comp
      ((((Ext.mk₀ x).comp hS.extClass (zero_add 1)).mapExactFunctor R).comp
        (Ext.mk₀ φ.τ₁) (add_zero 1)) (zero_add 1) =
      (Ext.mk₀ (z ≫ R.map x ≫ φ.τ₃)).comp hT.extClass (zero_add 1) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc_of_third_deg_zero, (hS.map_of_exact R).extClass_naturality hT φ]
  simp only [Ext.mk₀_comp_mk₀_assoc]

end ManuscriptAudit.ConnectingExtNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ConnectingExtNaturality.map_connecting
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
