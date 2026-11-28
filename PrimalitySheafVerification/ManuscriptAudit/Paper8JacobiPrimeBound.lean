import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiWeightCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimeSalieBound

/-! The Jacobi-twisted symmetric unit sum at a prime agrees exactly with the Salié sum. -/

namespace ManuscriptAudit.Paper8JacobiPrimeBound

open Finset Paper8JacobiWeightCRT Paper8ZModAdditiveCRT Paper8OddCrossJacobiSum
open Paper8PrimeQuadraticPhase Paper8PrimeSalieBound

noncomputable section

private def nonzeroEquivUnits (p : ℕ) [Fact p.Prime] : {x : ZMod p // x ≠ 0} ≃ (ZMod p)ˣ where
  toFun x := Units.mk0 x.1 x.2
  invFun x := ⟨x, x.ne_zero⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Units.ext rfl

theorem jacobi_sum_prime_eq_salie {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    twistedSymmetricUnitSum (jacobiUnitWeight p) a = primeSalieSum ZMod.stdAddChar a a := by
  let χ := primeQuadraticChar p
  let f (x : ZMod p) := χ x * ZMod.stdAddChar (a * x + a / x)
  have hSum : (∑ x : ZMod p, f x) = ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)), f x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · subst x
      simp [f, χ, primeQuadraticChar_apply]
    · rw [if_pos hx]
  have hJ (x : (ZMod p)ˣ) : jacobiUnitWeight p x = χ (x : ZMod p) := by
    unfold jacobiUnitWeight
    rw [← legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] <;> rfl
  unfold twistedSymmetricUnitSum primeSalieSum
  change _ = ∑ x : ZMod p, f x
  rw [hSum, Finset.sum_subtype (p := fun x : ZMod p => x ≠ 0) _ (by simp)]
  apply Fintype.sum_equiv (nonzeroEquivUnits p).symm _ _
  intro x
  have hX : ((nonzeroEquivUnits p).symm x).1 = (x : ZMod p) := rfl
  unfold f
  rw [hJ, hX, div_eq_mul_inv, ZMod.inv_coe_unit, mul_add]

theorem norm_jacobi_sum_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (jacobiUnitWeight p) a‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  rw [jacobi_sum_prime_eq_salie]
  exact norm_primeSalieSum_le hp (ZMod.isPrimitive_stdAddChar p) a ha.ne_zero

end
end ManuscriptAudit.Paper8JacobiPrimeBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8JacobiPrimeBound.norm_jacobi_sum_prime
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
