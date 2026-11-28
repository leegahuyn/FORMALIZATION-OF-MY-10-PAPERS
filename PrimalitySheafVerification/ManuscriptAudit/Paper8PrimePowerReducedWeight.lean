import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8WeightedUnitSumBridge
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenPrimePowerWeightedBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddPrimePowerWeightedBound

/-! Local square-root estimates for any bounded weight that descends modulo the odd prime. -/

namespace ManuscriptAudit.Paper8PrimePowerReducedWeight

open Paper8ZModAdditiveCRT Paper8ZModDigitOrthogonality Paper8ProductStationaryPhase
open Paper8WeightedUnitSumBridge Paper8EvenPrimePowerWeightedBound Paper8OddPrimePowerWeightedBound

noncomputable section

def primeReducedUnitWeight {p N : ℕ} (hd : p ∣ N) (w : ZMod p → ℂ) (x : (ZMod N)ˣ) : ℂ :=
  w (ZMod.castHom hd (ZMod p) (x : ZMod N))

private def LocalBound (p : ℕ) (w : ZMod p → ℂ) (N : ℕ) : Prop :=
  ∀ [NeZero N] (hd : p ∣ N) (a : ZMod N), IsUnit a →
    ‖twistedSymmetricUnitSum (primeReducedUnitWeight hd w) a‖ ≤ 2 * Real.sqrt (N : ℝ)

private theorem even_prime_reduced_bound {p r : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hr : 0 < r)
    (w : ZMod p → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1) : LocalBound p w (p ^ r * p ^ r) := by
  intro _ hd a ha
  let k := p ^ r
  let P : Nat.Prime p := Fact.out
  letI : NeZero p := ⟨P.ne_zero⟩
  letI : NeZero k := ⟨pow_ne_zero _ P.ne_zero⟩
  have hpk : p ∣ k := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    refine ⟨p ^ s, ?_⟩
    unfold k
    rw [hs, pow_succ, mul_comm]
  let f := ZMod.castHom hpk (ZMod p)
  let W (y : ZMod k) := w (f y)
  have hF : ZMod.castHom hd (ZMod p) = f.comp (@reduceLowDigit k k) := RingHom.ext_zmod _ _
  have hW : primeReducedUnitWeight hd w = fun x : (ZMod (k * k))ˣ =>
      W (reduceLowDigit (x : ZMod (k * k))) := by
    funext x
    unfold primeReducedUnitWeight W
    rw [hF, RingHom.comp_apply]
  change ‖twistedSymmetricUnitSum _ a‖ ≤ 2 * Real.sqrt ((k * k : ℕ) : ℝ)
  rw [hW, ← weightedSymmetricUnitSum_eq_twisted W a,
    Nat.cast_mul, ← pow_two, Real.sqrt_sq (Nat.cast_nonneg k)]
  exact norm_weighted_symmetric_sum_even_prime_power P hp hr W (fun x => hw (f x)) a ha

private theorem odd_prime_reduced_bound {p r : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hr : 0 < r)
    (w : ZMod p → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1) : LocalBound p w (p ^ r * (p * p ^ r)) := by
  intro _ hd a ha
  let k := p ^ r
  let m := p * k
  let P : Nat.Prime p := Fact.out
  letI : NeZero p := ⟨P.ne_zero⟩
  letI : NeZero k := ⟨pow_ne_zero _ P.ne_zero⟩
  let W (z : ZMod m) := w (reduceHighDigit z : ZMod p)
  have hF : ZMod.castHom hd (ZMod p) = (@reduceHighDigit p k).comp (@reduceLowDigit k m) :=
    RingHom.ext_zmod _ _
  have hW : primeReducedUnitWeight hd w = fun x : (ZMod (k * m))ˣ =>
      W (reduceLowDigit (x : ZMod (k * m))) := by
    funext x
    unfold primeReducedUnitWeight W
    rw [hF, RingHom.comp_apply]
  have hS : Real.sqrt ((k * m : ℕ) : ℝ) = (k : ℝ) * Real.sqrt (p : ℝ) := by
    rw [show k * m = p * (k * k) by unfold m; ring,
      Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p), ← pow_two, Real.sqrt_sq (Nat.cast_nonneg k)]
    ring
  change ‖twistedSymmetricUnitSum _ a‖ ≤ 2 * Real.sqrt ((k * m : ℕ) : ℝ)
  rw [hW, ← weightedSymmetricUnitSum_eq_twisted W a, hS, ← mul_assoc]
  exact norm_weighted_symmetric_sum_odd_prime_power hp hr w hw a ha

theorem norm_prime_reduced_unit_sum {p e : ℕ} [Fact p.Prime] [NeZero (p ^ e)]
    (hp : p ≠ 2) (he : 2 ≤ e) (hd : p ∣ p ^ e) (w : ZMod p → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (a : ZMod (p ^ e)) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (primeReducedUnitWeight hd w) a‖ ≤ 2 * Real.sqrt ((p ^ e : ℕ) : ℝ) := by
  let r := e / 2
  have hr : 0 < r := by unfold r; omega
  by_cases hParity : e % 2 = 0
  · have hE : e = r + r := by unfold r; omega
    have hN : p ^ e = p ^ r * p ^ r := by rw [← pow_add, ← hE]
    have hLoc : LocalBound p w (p ^ e) := hN.symm ▸ even_prime_reduced_bound hp hr w hw
    exact hLoc hd a ha
  · have hE : e = r + (1 + r) := by unfold r; omega
    have hN : p ^ e = p ^ r * (p * p ^ r) := by rw [hE, pow_add, pow_add, pow_one]
    have hLoc : LocalBound p w (p ^ e) := hN.symm ▸ odd_prime_reduced_bound hp hr w hw
    exact hLoc hd a ha

end
end ManuscriptAudit.Paper8PrimePowerReducedWeight

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8PrimePowerReducedWeight.norm_prime_reduced_unit_sum
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
