import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormNum

/-!
# A degree drop defeats the unrestricted discriminant criterion

The integral polynomial 2X has degree one, hence discriminant one.
Modulo 2 both it and its derivative are zero. Over the 2-adic integers
it nevertheless has just the root zero. This tests the converse that
a unique lift implies a simple root under discriminant nonvanishing
alone, without a hypothesis on the leading coefficient.
-/

namespace ManuscriptAudit.PadicDiscriminantDegreeDrop

open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def doubledVariable : ℤ[X] := C 2 * X

theorem doubledVariable_degree : doubledVariable.degree = 1 := by
  unfold doubledVariable
  rw [Polynomial.degree_mul_X, Polynomial.degree_C (by decide : (2 : ℤ) ≠ 0), zero_add]

theorem doubledVariable_discriminant : doubledVariable.discr = 1 :=
  Polynomial.discr_of_degree_eq_one doubledVariable_degree

theorem doubledVariable_residue_zero :
    doubledVariable.map (Int.castRingHom (ZMod 2)) = 0 := by
  have hTwo : (Int.castRingHom (ZMod 2)) 2 = 0 := by decide
  simp only [doubledVariable, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    hTwo, Polynomial.C_0, zero_mul]

theorem doubledVariable_unique_two_adic_lift :
    ∃! z : ℤ_[2], (doubledVariable.map (Int.castRingHom (ℤ_[2]))).eval z = 0 ∧
      PadicInt.toZMod z = (0 : ZMod 2) := by
  refine ⟨0, by simp [doubledVariable], ?_⟩
  intro z hz
  have h : (2 : ℤ_[2]) * z = 0 := by
    simpa [doubledVariable] using hz.1
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem discr_nonzero_unique_lift_with_repeated_residue :
    (doubledVariable.discr : ZMod 2) ≠ 0 ∧
    ((doubledVariable.map (Int.castRingHom (ZMod 2))).derivative.eval 0 = 0) ∧
    ∃! z : ℤ_[2], (doubledVariable.map (Int.castRingHom (ℤ_[2]))).eval z = 0 ∧
      PadicInt.toZMod z = (0 : ZMod 2) := by
  exact ⟨by simp [doubledVariable_discriminant], by simp [doubledVariable_residue_zero],
    doubledVariable_unique_two_adic_lift⟩

end

end ManuscriptAudit.PadicDiscriminantDegreeDrop

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicDiscriminantDegreeDrop.doubledVariable_degree,
      ``ManuscriptAudit.PadicDiscriminantDegreeDrop.doubledVariable_discriminant,
      ``ManuscriptAudit.PadicDiscriminantDegreeDrop.doubledVariable_residue_zero,
      ``ManuscriptAudit.PadicDiscriminantDegreeDrop.doubledVariable_unique_two_adic_lift,
      ``ManuscriptAudit.PadicDiscriminantDegreeDrop.discr_nonzero_unique_lift_with_repeated_residue] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
