import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiWeightCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8WeightedUnitSumBridge
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenPrimePowerWeightedBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddPrimePowerWeightedBound

/-! Native Jacobi-twisted local estimates for both non-prime odd prime-power exponents. -/

namespace ManuscriptAudit.Paper8JacobiPrimePowerBound

open Paper8JacobiWeightCRT Paper8ZModAdditiveCRT Paper8OddCrossJacobiSum Paper8PrimeQuadraticPhase
open Paper8EvenPrimePowerWeightedBound Paper8OddPrimePowerWeightedBound Paper8ProductStationaryPhase
open Paper8WeightedUnitSumBridge Paper8ZModDigitOrthogonality

noncomputable section

private theorem prime_dvd_pos_power {p r : ℕ} (hr : 0 < r) : p ∣ p ^ r := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  refine ⟨p ^ j, ?_⟩
  rw [hj, pow_succ, mul_comm]

private theorem jacobi_weight_of_prime_power_eq {p e N : ℕ} [Fact p.Prime] (hN : N = p ^ e)
    (hd : p ∣ N) (x : (ZMod N)ˣ) :
    jacobiUnitWeight N x = primeQuadraticChar p (ZMod.castHom hd (ZMod p) (x : ZMod N)) ^ e := by
  subst N
  exact jacobiUnitWeight_prime_power hd x

private theorem norm_primeQuadraticChar_power_le {p e : ℕ} [Fact p.Prime] (he : 0 < e) (x : ZMod p) :
    ‖primeQuadraticChar p x ^ e‖ ≤ 1 := by
  by_cases hx : x = 0
  · have h : primeQuadraticChar p (0 : ZMod p) = 0 := by simp [primeQuadraticChar_apply]
    rw [hx, h, zero_pow he.ne', norm_zero]
    norm_num
  · rw [norm_pow, norm_primeQuadraticChar hx, one_pow] <;> exact le_rfl

theorem norm_jacobi_sum_even_prime_power {p r : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : 0 < r) (a : ZMod (p ^ r * p ^ r)) (ha : IsUnit a) :
    letI : NeZero (p ^ r * p ^ r) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
    ‖twistedSymmetricUnitSum (jacobiUnitWeight (p ^ r * p ^ r)) a‖ ≤ 2 * ((p ^ r : ℕ) : ℝ) := by
  let k := p ^ r
  let P : Nat.Prime p := Fact.out
  letI : NeZero p := ⟨P.ne_zero⟩
  letI : NeZero k := ⟨pow_ne_zero _ P.ne_zero⟩
  have hEq : k * k = p ^ (2 * r) := by
    unfold k
    rw [← pow_add]
    congr 1
    omega
  have hd : p ∣ k * k := (prime_dvd_pos_power hr).trans (dvd_mul_right k k)
  have hJ (x : (ZMod (k * k))ˣ) : jacobiUnitWeight (k * k) x = 1 := by
    have hx : ZMod.castHom hd (ZMod p) (x : ZMod (k * k)) ≠ 0 :=
      (x.isUnit.map (ZMod.castHom hd (ZMod p))).ne_zero
    rw [jacobi_weight_of_prime_power_eq hEq hd, pow_mul, primeQuadraticChar_sq hx, one_pow]
  change ‖twistedSymmetricUnitSum (jacobiUnitWeight (k * k)) a‖ ≤ 2 * (k : ℝ)
  rw [show jacobiUnitWeight (k * k) = fun _ => 1 from funext hJ]
  have hW := weightedSymmetricUnitSum_eq_twisted (fun _ : ZMod k => (1 : ℂ)) a
  change _ = twistedSymmetricUnitSum (fun _ => 1) a at hW
  rw [← hW]
  exact norm_weighted_symmetric_sum_even_prime_power P hp hr _ (fun _ => by simp) a ha

theorem norm_jacobi_sum_odd_prime_power {p r : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : 0 < r) (a : ZMod (p ^ r * (p * p ^ r))) (ha : IsUnit a) :
    letI : NeZero (p ^ r * (p * p ^ r)) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (mul_ne_zero (Fact.out : p.Prime).ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))⟩
    ‖twistedSymmetricUnitSum (jacobiUnitWeight (p ^ r * (p * p ^ r))) a‖ ≤
      2 * ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
  let k := p ^ r
  let m := p * k
  let e := r + (1 + r)
  let P : Nat.Prime p := Fact.out
  letI : NeZero p := ⟨P.ne_zero⟩
  letI : NeZero k := ⟨pow_ne_zero _ P.ne_zero⟩
  have he : 0 < e := by unfold e; omega
  have hEq : k * m = p ^ e := by
    unfold k m e
    rw [pow_add, pow_add, pow_one]
  have hd : p ∣ k * m := (prime_dvd_pos_power hr).trans (dvd_mul_right k m)
  let w (x : ZMod p) := primeQuadraticChar p x ^ e
  let W (b : ZMod m) := w (reduceHighDigit b : ZMod p)
  have hF : ZMod.castHom hd (ZMod p) =
      (@reduceHighDigit p k).comp (@reduceLowDigit k m) := RingHom.ext_zmod _ _
  have hJ (x : (ZMod (k * m))ˣ) : jacobiUnitWeight (k * m) x = W (reduceLowDigit (x : ZMod (k * m))) := by
    rw [jacobi_weight_of_prime_power_eq hEq hd, hF] <;> rfl
  change ‖twistedSymmetricUnitSum (jacobiUnitWeight (k * m)) a‖ ≤ 2 * (k : ℝ) * Real.sqrt (p : ℝ)
  rw [show jacobiUnitWeight (k * m) = fun x => W (reduceLowDigit (x : ZMod (k * m))) from funext hJ,
    ← weightedSymmetricUnitSum_eq_twisted W a]
  exact norm_weighted_symmetric_sum_odd_prime_power hp hr w (norm_primeQuadraticChar_power_le he) a ha

end
end ManuscriptAudit.Paper8JacobiPrimePowerBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8JacobiPrimePowerBound.norm_jacobi_sum_even_prime_power,
      ``ManuscriptAudit.Paper8JacobiPrimePowerBound.norm_jacobi_sum_odd_prime_power] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
