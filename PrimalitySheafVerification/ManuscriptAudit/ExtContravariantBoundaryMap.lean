import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Compatibility of contravariant connecting homomorphisms with an exact functor. -/

namespace ManuscriptAudit.ExtContravariantBoundaryMap

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

theorem map_boundary (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex C} (hS : S.ShortExact) {T : ShortComplex D} (hT : T.ShortExact)
    (φ : T ⟶ S.map L) {A : C} (n : ℕ) (x : Ext S.X₁ A n) :
    (Ext.mk₀ φ.τ₃).comp
        ((hS.extClass.comp x (Nat.add_comm 1 n)).mapExactFunctor L) (zero_add (n+1)) =
      hT.extClass.comp ((Ext.mk₀ φ.τ₁).comp (x.mapExactFunctor L) (zero_add n))
        (Nat.add_comm 1 n) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  let hL := hS.map_of_exact L
  let x' := x.mapExactFunctor L
  have hNat := hT.extClass_naturality hL φ
  calc
    (Ext.mk₀ φ.τ₃).comp (hL.extClass.comp x' (Nat.add_comm 1 n)) (zero_add (n+1)) =
        ((Ext.mk₀ φ.τ₃).comp hL.extClass (zero_add 1)).comp x' (Nat.add_comm 1 n) :=
      (Ext.comp_assoc (Ext.mk₀ φ.τ₃) hL.extClass x' (zero_add 1)
        (Nat.add_comm 1 n) (by omega)).symm
    _ = (hT.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1)).comp x' (Nat.add_comm 1 n) := by
      rw [hNat]
    _ = hT.extClass.comp ((Ext.mk₀ φ.τ₁).comp x' (zero_add n)) (Nat.add_comm 1 n) :=
      Ext.comp_assoc_of_second_deg_zero _ _ _ _

end ManuscriptAudit.ExtContravariantBoundaryMap

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtContravariantBoundaryMap.map_boundary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
