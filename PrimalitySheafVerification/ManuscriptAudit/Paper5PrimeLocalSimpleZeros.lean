import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualLocalZetaZeros
import PrimalitySheafVerification.ManuscriptAudit.Paper7FiniteEulerSimpleRoots

/-! The actual local zeta has simple zeros at every good prime. -/

namespace ManuscriptAudit.Paper5PrimeLocalSimpleZeros

open Polynomial Paper5ActualHasseWeil Paper5ActualAnalyticLocalZeta Paper5ActualLocalZetaPoles
open Paper7FiniteEulerSimpleRoots (prime_trace_root_derivative_ne_zero)

noncomputable section

theorem rational_zeta_derivative_ne_zero_at_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (A : ZMod p) {z : ℂ} (hz : z ∈ awayFromPoles (p : ℂ))
    (h : rationalZeta (p : ℂ) (firstTrace p A : ℂ) z = 0) :
    deriv (rationalZeta (p : ℂ) (firstTrace p A : ℂ)) z ≠ 0 := by
  let a := firstTrace p A
  let P : ℂ[X] := 1 - C (a : ℂ)*X + C (p : ℂ)*X^2
  let D : ℂ → ℂ := fun w => (1-w)*(1-(p : ℂ)*w)
  change z ≠ 1 ∧ z ≠ (p : ℂ)⁻¹ at hz
  have hp₀ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz₁ : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hz₂ : 1-(p : ℂ)*z ≠ 0 := by
    intro he
    apply hz.2
    have hq : (p : ℂ)*z = 1 := (sub_eq_zero.mp he).symm
    calc
      z = (p : ℂ)⁻¹ * ((p : ℂ)*z) := by field_simp [hp₀]
      _ = (p : ℂ)⁻¹ := by rw [hq, mul_one]
  have hzD : D z ≠ 0 := mul_ne_zero hz₁ hz₂
  have hEval (w : ℂ) : P.eval w = 1-(a : ℂ)*w+(p : ℂ)*w^2 := by simp [P]
  have hR : (fun w => P.eval w / D w) = rationalZeta (p : ℂ) (a : ℂ) := by
    funext w
    unfold rationalZeta D
    rw [hEval]
  have hDiv : P.eval z / D z = 0 := (congrFun hR z).trans h
  have hPz : P.eval z = 0 := ((div_eq_zero_iff.mp hDiv).resolve_right hzD)
  have hp' : P.derivative.eval z ≠ 0 :=
    prime_trace_root_derivative_ne_zero (Fact.out : p.Prime) hp a ((hEval z).symm.trans hPz)
  have hD : DifferentiableAt ℂ D z := by
    unfold D
    fun_prop
  have hDeriv : HasDerivAt (fun w => P.eval w / D w)
      ((P.derivative.eval z * D z - P.eval z * deriv D z) / D z^2) z :=
    (P.hasDerivAt z).div hD.hasDerivAt hzD
  rw [← hR, hDeriv.deriv, hPz, zero_mul, sub_zero]
  exact div_ne_zero (mul_ne_zero hp' hzD) (pow_ne_zero _ hzD)

end
end ManuscriptAudit.Paper5PrimeLocalSimpleZeros

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5PrimeLocalSimpleZeros.rational_zeta_derivative_ne_zero_at_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
