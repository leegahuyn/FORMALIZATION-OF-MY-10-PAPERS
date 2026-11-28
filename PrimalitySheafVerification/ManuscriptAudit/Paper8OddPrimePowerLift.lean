import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerDigitSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddPrimePowerGaussBranch

/-! Controlled changes of digit lifts in the odd prime-power stationary branches. -/

namespace ManuscriptAudit.Paper8OddPrimePowerLift

open Finset Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality Paper8PrimePowerStationaryPhase
open Paper8OddPrimePowerGaussBranch

noncomputable section

theorem reduceLowDigit_apply {n m : ℕ} [NeZero n] [NeZero m] (z : ZMod (n * m)) :
    reduceLowDigit z = (z.val : ZMod m) := by
  calc
    _ = reduceLowDigit ((z.val : ℕ) : ZMod (n * m)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast reduceLowDigit _

theorem lowDigit_mul_shift {p k : ℕ} [NeZero p] [NeZero k] (z : ZMod p) (s : ℕ) :
    (k : ZMod (p * k)) * ((z + (s : ZMod p)).val : ZMod (p * k)) =
      (k : ZMod (p * k)) * (z.val : ZMod (p * k)) + (k : ZMod (p * k)) * (s : ZMod (p * k)) := by
  let a : ℤ := (z.val : ℤ) + (s : ℤ)
  let b : ℤ := (z + (s : ZMod p)).val
  have hz : (b : ZMod p) = (a : ZMod p) := by
    unfold a b
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a p).1 hz
  have hQ := congrArg (fun t : ℤ => (t : ZMod (p * k))) hq
  change (((a - b : ℤ)) : ZMod (p * k)) = (((p : ℤ) * q : ℤ) : ZMod (p * k)) at hQ
  unfold a b at hQ
  push_cast at hQ
  have hK : (p : ZMod (p * k)) * (k : ZMod (p * k)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  linear_combination -(k : ZMod (p * k)) * hQ - (q : ZMod (p * k)) * hK

theorem norm_odd_branch_modulus_congr {p r M : ℕ} [Fact p.Prime] [NeZero M]
    (hM : M = p * (p ^ r * p ^ r)) (hp : p ≠ 2) (hr : 0 < r)
    (a e : ZMod M) (ha : IsUnit a) (he : e ^ 2 = 1) :
    ‖∑ z : ZMod p, symmetricPhase a (e + (p ^ r : ZMod M) * (z.val : ZMod M))‖ =
      Real.sqrt (p : ℝ) := by
  subst M
  simpa only [symmetricPhase, Nat.cast_pow] using norm_odd_prime_power_branch hp hr a e ha he

theorem stationary_lift_phase_at_sign {p k : ℕ} [NeZero p] [NeZero k]
    (hd : p ∣ k) (a e X : ZMod (k * (p * k))) (he : e ^ 2 = 1) (z : ZMod p)
    (hX : reduceLowDigit X = reduceLowDigit (e + (k : ZMod (k * (p * k))) *
      (z.val : ZMod (k * (p * k))))) :
    symmetricPhase a X = symmetricPhase a (e + (k : ZMod (k * (p * k))) * (z.val : ZMod (k * (p * k)))) := by
  let M := k * (p * k)
  let Z := e + (k : ZMod M) * (z.val : ZMod M)
  let f := @reduceHighDigit k (p * k)
  have hZ : f Z = f e := by
    unfold Z
    rw [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
  have hZ2 : f Z ^ 2 = 1 := by
    have h := congrArg f he
    rw [map_pow, map_one] at h
    rwa [hZ]
  have hZunit : IsUnit Z := by
    have hD : M ∣ k ^ 3 := by
      obtain ⟨q, hq⟩ := hd
      refine ⟨q, ?_⟩
      calc
        _ = k * (k * k) := by ring
        _ = _ := by unfold M; nth_rw 2 [hq]; ring
    have hK : (k : ZMod M) ^ 3 = 0 := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_zero_iff _ M).2 hD
    let T := (k : ZMod M) * (z.val : ZMod M)
    have hT : T ^ 3 = 0 := by unfold T; rw [mul_pow, hK, zero_mul]
    have hh := quadratic_nilpotent_inverse he hT
    exact ⟨⟨_, _, hh, by simpa only [mul_comm] using hh⟩, rfl⟩
  have hC : reduceHighDigit (a * (1 - (Z⁻¹) ^ 2)) = 0 := by
    have hFInv : f (Z⁻¹) = (f Z)⁻¹ := by
      have hP := congrArg f (ZMod.mul_inv_of_unit Z hZunit)
      rw [map_mul, map_one] at hP
      exact (ZMod.inv_eq_of_mul_eq_one _ _ _ hP).symm
    have hQ : ((f Z)⁻¹) ^ 2 = 1 := by
      have hP : f Z ^ 2 * (f Z)⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, ZMod.mul_inv_of_unit _ (hZunit.map f), one_pow]
      simpa only [hZ2, one_mul] using hP
    change f (a * (1 - Z⁻¹ ^ 2)) = 0
    rw [map_mul, map_sub, map_one, map_pow, hFInv, hQ, sub_self, mul_zero]
  exact symmetricPhase_eq_of_stationary_lift (dvd_mul_left k p) a Z X hZunit hC hX

end
end ManuscriptAudit.Paper8OddPrimePowerLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddPrimePowerLift.lowDigit_mul_shift,
      ``ManuscriptAudit.Paper8OddPrimePowerLift.stationary_lift_phase_at_sign] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
