import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Identity gluing of free module coordinates

Compatible vectors with identity transition are coordinatewise copies
of the fiber product of the coefficient rings. A verified pullback
identification of the coefficient rings therefore gives a basis.
-/

namespace ManuscriptAudit.MilnorIdentityGluing

noncomputable section

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

/-- A pair of scalars is compatible at the common quotient. -/
def compatiblePair : Submodule A (B × C) where
  carrier := {x | q x.1 = s x.2}
  zero_mem' := by
    change q 0 = s 0
    rw [map_zero, map_zero]
  add_mem' {x y} hx hy := by
    have hx' : q x.1 = s x.2 := hx
    have hy' : q y.1 = s y.2 := hy
    change q (x.1 + y.1) = s (x.2 + y.2)
    rw [map_add, map_add, hx', hy']
  smul_mem' a {x} hx := by
    have hx' : q x.1 = s x.2 := hx
    change q (a • x.1) = s (a • x.2)
    calc
      q (a • x.1) = a • q x.1 := q.toLinearMap.map_smul a x.1
      _ = a • s x.2 := congrArg (a • ·) hx'
      _ = s (a • x.2) := (s.toLinearMap.map_smul a x.2).symm

/-- The coefficient map into the actual compatible pairs. -/
def pairMap : A →ₗ[A] compatiblePair q s where
  toFun a := ⟨(algebraMap A B a, algebraMap A C a), by
    change q (algebraMap A B a) = s (algebraMap A C a)
    rw [q.commutes, s.commutes]⟩
  map_add' a b := by
    apply Subtype.ext
    exact Prod.ext (map_add (algebraMap A B) a b) (map_add (algebraMap A C) a b)
  map_smul' a b := by
    apply Subtype.ext
    change (algebraMap A B (a * b), algebraMap A C (a * b)) =
      (a • algebraMap A B b, a • algebraMap A C b)
    have hB : algebraMap A B (a * b) = a • algebraMap A B b := by
      rw [map_mul, Algebra.smul_def]
    have hC : algebraMap A C (a * b) = a • algebraMap A C b := by
      rw [map_mul, Algebra.smul_def]
    exact Prod.ext hB hC

include q s
variable (ι : Type*)

/-- Identity gluing as a submodule of a genuine pair of coordinate spaces. -/
def identityPatch : Submodule A ((ι → B) × (ι → C)) where
  carrier := {x | ∀ i, (x.1 i, x.2 i) ∈ compatiblePair q s}
  zero_mem' := fun _ => (compatiblePair q s).zero_mem
  add_mem' {_ _} hx hy := fun i => (compatiblePair q s).add_mem (hx i) (hy i)
  smul_mem' a {_} hx := fun i => (compatiblePair q s).smul_mem a (hx i)

/-- Transpose an array of compatible scalar pairs into compatible vectors. -/
def coordinatesEquiv : (ι → compatiblePair q s) ≃ₗ[A] identityPatch q s ι where
  toFun x :=
    ⟨(fun i => (x i).val.1, fun i => (x i).val.2), fun i => (x i).property⟩
  invFun x i := ⟨(x.val.1 i, x.val.2 i), x.property i⟩
  left_inv x := by funext i; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; exact Prod.ext rfl rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl

/-- Identity patching over a coefficient pullback recovers free coordinates. -/
def identityPatchEquiv (h : Function.Bijective (pairMap q s)) :
    (ι → A) ≃ₗ[A] identityPatch q s ι :=
  (LinearEquiv.piCongrRight (fun _ : ι => LinearEquiv.ofBijective (pairMap q s) h)).trans
    (coordinatesEquiv q s ι)

/-- Identity gluing of finitely many free coordinates is finite and free. -/
theorem identityPatch_finite_free [Fintype ι] (h : Function.Bijective (pairMap q s)) :
    Module.Finite A (identityPatch q s ι) ∧ Module.Free A (identityPatch q s ι) := by
  classical
  let e := identityPatchEquiv q s ι h
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Free.of_basis ((Pi.basisFun A ι).map e)⟩

end

end ManuscriptAudit.MilnorIdentityGluing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.MilnorIdentityGluing.coordinatesEquiv,
      ``ManuscriptAudit.MilnorIdentityGluing.identityPatchEquiv,
      ``ManuscriptAudit.MilnorIdentityGluing.identityPatch_finite_free] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
