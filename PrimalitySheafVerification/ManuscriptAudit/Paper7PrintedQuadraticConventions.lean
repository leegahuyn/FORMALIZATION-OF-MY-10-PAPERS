import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper7ActualCommonEuler

/-! The reciprocal pp. 280–281 and monic p. 289 polynomials at their actual common argument. -/

namespace ManuscriptAudit.Paper7PrintedQuadraticConventions

open Paper7ActualCommonEuler Paper7CommonEulerLocalDecay

def monic (p : ℕ) (a z : ℂ) : ℂ := z^2 - a*z + (p : ℂ)

theorem reciprocal_evaluation (p : ℕ) (a z : ℂ) (hz : z ≠ 0) :
    z^2 * denominator p a z⁻¹ = monic p a z := by
  unfold denominator monic
  field_simp [hz] <;> ring

theorem monic_ne_printed_local_denominator (n : ℕ) :
    monic (goodPrime n) (trace n) ≠ denominator (goodPrime n) (trace n) := by
  intro he
  have h := congrFun he 0
  have hC : (goodPrime n : ℂ) = 1 := by
    simpa [monic, denominator] using h
  have hn : goodPrime n = 1 := by exact_mod_cast hC
  have h5 := goodPrime_atLeastFive n
  omega

theorem reciprocal_local_factors_disagree_at_zero (n : ℕ) :
    (monic (goodPrime n) (trace n) 0)⁻¹ ≠
      (denominator (goodPrime n) (trace n) 0)⁻¹ := by
  intro h
  have he := congrArg Inv.inv h
  simp only [inv_inv, monic, denominator, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero, zero_add, add_zero] at he
  have hn : goodPrime n = 1 := by exact_mod_cast he
  have h5 := goodPrime_atLeastFive n
  omega

end ManuscriptAudit.Paper7PrintedQuadraticConventions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7PrintedQuadraticConventions.reciprocal_evaluation,
      ``ManuscriptAudit.Paper7PrintedQuadraticConventions.monic_ne_printed_local_denominator,
      ``ManuscriptAudit.Paper7PrintedQuadraticConventions.reciprocal_local_factors_disagree_at_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
