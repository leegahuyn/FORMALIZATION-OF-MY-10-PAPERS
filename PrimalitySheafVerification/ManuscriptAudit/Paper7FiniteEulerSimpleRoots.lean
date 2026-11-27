import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.EllipticQuadraticRadius
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerFinitePoles

/-! All poles of the actual finite common-parameter products are simple. -/

namespace ManuscriptAudit.Paper7FiniteEulerSimpleRoots

open Polynomial Paper7ActualCommonEuler Paper7CommonEulerLocalDecay
open Paper7CommonEulerFinitePoles EllipticQuadraticRadius

noncomputable section

def quadratic (j : ℕ) : ℂ[X] :=
  1 - C (trace j) * X + C (goodPrime j : ℂ) * X^2

private theorem eval_quadratic (j : ℕ) (z : ℂ) :
    (quadratic j).eval z = denominator (goodPrime j) (trace j) z := by
  simp [quadratic, denominator]

private theorem square_trace_ne (j : ℕ) :
    trace j ^ 2 ≠ 4 * (goodPrime j : ℂ) := by
  intro h
  change ((signedTrace j : ℤ) : ℂ)^2 = 4 * (goodPrime j : ℂ) at h
  have hZ : signedTrace j ^ 2 = 4 * (goodPrime j : ℤ) := by exact_mod_cast h
  have hN : (signedTrace j).natAbs^2 = 4 * goodPrime j := by
    simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast]
      using congrArg Int.natAbs hZ
  have hp : (goodPrime j).Prime := goodPrime_prime j
  have hp5 := goodPrime_atLeastFive j
  have hd : goodPrime j ∣ (signedTrace j).natAbs^2 :=
    ⟨4, hN.trans (Nat.mul_comm 4 (goodPrime j))⟩
  have hPos : 0 < (signedTrace j).natAbs := by
    by_contra! hz
    have hz' : (signedTrace j).natAbs = 0 := by omega
    rw [hz'] at hN
    norm_num at hN
    omega
  have hle := Nat.le_of_dvd hPos (hp.dvd_of_dvd_pow hd)
  have hsq : goodPrime j ^ 2 ≤ (signedTrace j).natAbs^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hle hle
  have hlt : 4 * goodPrime j < goodPrime j ^ 2 := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hp.pos
  exact hlt.not_ge (hN ▸ hsq)

theorem local_root_derivative_ne_zero (j : ℕ) {z : ℂ}
    (h : denominator (goodPrime j) (trace j) z = 0) :
    (quadratic j).derivative.eval z ≠ 0 := by
  intro hd
  have hd' : -trace j + 2 * (goodPrime j : ℂ) * z = 0 := by
    have hDer : (quadratic j).derivative.eval z =
        -trace j + 2 * (goodPrime j : ℂ) * z := by
      simp [quadratic, derivative_X_pow]
      <;> ring
    exact hDer.symm.trans hd
  apply square_trace_ne j
  unfold denominator at h
  linear_combination (-4 * (goodPrime j : ℂ)) * h +
    (-trace j + 2 * (goodPrime j : ℂ) * z) * hd'

theorem local_root_norm (j : ℕ) {z : ℂ}
    (h : denominator (goodPrime j) (trace j) z = 0) :
    ‖z‖ = (Real.sqrt (goodPrime j : ℝ))⁻¹ := by
  have hp : 0 < (goodPrime j : ℝ) := by exact_mod_cast (goodPrime_prime j).pos
  have ha := trace_hasse j
  change ‖((signedTrace j : ℤ) : ℂ)‖ ≤ 2 * Real.sqrt (goodPrime j : ℝ) at ha
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at ha
  have hRoot : (localPolynomial (goodPrime j : ℝ) (signedTrace j : ℝ)).IsRoot z := by
    rw [Polynomial.IsRoot, eval_localPolynomial]
    simpa only [expression, denominator, Complex.ofReal_intCast, Complex.ofReal_natCast] using h
  simpa only [one_div] using
    ((all_roots_radius_iff (goodPrime j : ℝ) (signedTrace j : ℝ) hp).2 ha) z hRoot

theorem shared_root_same_prime_index (j k : ℕ) {z : ℂ}
    (hj : denominator (goodPrime j) (trace j) z = 0)
    (hk : denominator (goodPrime k) (trace k) z = 0) : j = k := by
  have hh := inv_injective ((local_root_norm j hj).symm.trans (local_root_norm k hk))
  have hpj : 0 ≤ (goodPrime j : ℝ) := by positivity
  have hpk : 0 ≤ (goodPrime k : ℝ) := by positivity
  have hSq := congrArg (fun x : ℝ => x^2) hh
  rw [Real.sq_sqrt hpj, Real.sq_sqrt hpk] at hSq
  have hPrime : goodPrime j = goodPrime k := by exact_mod_cast hSq
  have hjk := (Nat.nth_le_nth Nat.infinite_setOf_prime).mp hPrime.le
  have hkj := (Nat.nth_le_nth Nat.infinite_setOf_prime).mp hPrime.ge
  omega

theorem denominator_root_is_simple (n : ℕ) {z : ℂ}
    (h : (denominatorPolynomial n).eval z = 0) :
    (denominatorPolynomial n).derivative.eval z ≠ 0 := by
  classical
  rw [eval_denominatorPolynomial] at h
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp h
  let Q : ℂ[X] := ∏ k ∈ (Finset.range n).erase j, quadratic k
  have hF : denominatorPolynomial n = quadratic j * Q := by
    exact (Finset.mul_prod_erase (s := Finset.range n) quadratic hj).symm
  have hZq : (quadratic j).eval z = 0 := (eval_quadratic j z).trans hz
  have hNZ : Q.eval z ≠ 0 := by
    rw [show Q = ∏ k ∈ (Finset.range n).erase j, quadratic k from rfl, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk he
    exact (Finset.mem_erase.mp hk).1 (shared_root_same_prime_index k j
      ((eval_quadratic k z).symm.trans he) hz)
  rw [hF, derivative_mul, eval_add, eval_mul, eval_mul, hZq, zero_mul, add_zero]
  exact mul_ne_zero (local_root_derivative_ne_zero j hz) hNZ

end
end ManuscriptAudit.Paper7FiniteEulerSimpleRoots

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7FiniteEulerSimpleRoots.local_root_derivative_ne_zero,
      ``ManuscriptAudit.Paper7FiniteEulerSimpleRoots.local_root_norm,
      ``ManuscriptAudit.Paper7FiniteEulerSimpleRoots.shared_root_same_prime_index,
      ``ManuscriptAudit.Paper7FiniteEulerSimpleRoots.denominator_root_is_simple] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
