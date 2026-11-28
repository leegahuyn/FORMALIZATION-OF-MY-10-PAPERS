import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerStationaryPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModDigitOrthogonality
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimeQuadraticPhase

/-! Each odd prime-power stationary branch is exactly a complete prime Gauss sum. -/

namespace ManuscriptAudit.Paper8OddPrimePowerGaussBranch

open Finset AddChar Paper8PrimePowerStationaryPhase Paper8ZModDigitOrthogonality Paper8PrimeQuadraticPhase

noncomputable section

private theorem stdAddChar_high_digit_nat {n m : ℕ} [NeZero n] [NeZero m]
    (z : ZMod (n * m)) (d : ℕ) :
    ZMod.stdAddChar ((m : ZMod (n * m)) * z * (d : ZMod (n * m))) =
      ZMod.stdAddChar (reduceHighDigit z * (d : ZMod n)) := by
  let a : ZMod n := d
  have hVal : a.val = d % n := ZMod.val_natCast n d
  have hD := congrArg (fun t : ℕ => (t : ZMod (n * m))) (Nat.mod_add_div d n)
  push_cast at hD
  have hKill : (m : ZMod (n * m)) * (n : ZMod (n * m)) = 0 := by
    rw [mul_comm, ← Nat.cast_mul, ZMod.natCast_self]
  have hEq : (m : ZMod (n * m)) * z * (d : ZMod (n * m)) =
      (m : ZMod (n * m)) * z * (a.val : ZMod (n * m)) := by
    rw [hVal]
    conv_lhs => rw [← hD, mul_add]
    have hZero : (m : ZMod (n * m)) * z * ((n : ZMod (n * m)) * ((d / n : ℕ) : ZMod (n * m))) = 0 := by
      calc
        _ = ((m : ZMod (n * m)) * (n : ZMod (n * m))) * (z * ((d / n : ℕ) : ZMod (n * m))) := by ring
        _ = _ := by rw [hKill, zero_mul]
    rw [hZero, add_zero]
  rw [hEq, stdAddChar_high_digit] <;> rfl

private theorem norm_stdAddChar {n : ℕ} [NeZero n] (a : ZMod n) : ‖ZMod.stdAddChar a‖ = 1 := by
  have hn : 0 < ringChar (ZMod n) := by rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne _)
  exact Complex.norm_eq_one_of_mem_rootsOfUnity ((ZMod.stdAddChar (N := n)).val_mem_rootsOfUnity a hn)

theorem norm_odd_prime_power_branch {p r : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hr : 0 < r)
    (a e : ZMod (p * (p ^ r * p ^ r))) (hA : IsUnit a) (he : e ^ 2 = 1) :
    ‖∑ z : ZMod p, ZMod.stdAddChar (a *
      ((e + ((p ^ r : ℕ) : ZMod (p * (p ^ r * p ^ r))) * (z.val : ZMod (p * (p ^ r * p ^ r)))) +
       (e + ((p ^ r : ℕ) : ZMod (p * (p ^ r * p ^ r))) * (z.val : ZMod (p * (p ^ r * p ^ r))))⁻¹))‖ =
      Real.sqrt (p : ℝ) := by
  let k : ℕ := p ^ r
  let M : ℕ := p * (k * k)
  let f : ZMod M →+* ZMod p := @reduceHighDigit p (k * k)
  let T (z : ZMod p) : ZMod M := (k : ZMod M) * (z.val : ZMod M)
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hD : p ∣ k := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    refine ⟨p ^ s, ?_⟩
    unfold k
    rw [hs, pow_succ, mul_comm]
  have hDM : M ∣ k ^ 3 := by
    obtain ⟨m, hm⟩ := hD
    refine ⟨m, ?_⟩
    calc
      _ = k * (k * k) := by ring
      _ = _ := by nth_rw 1 [hm]; unfold M; ring
  have hK : ((k : ZMod M) ^ 3) = 0 := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff _ M).2 hDM
  have hT (z : ZMod p) : T z ^ 3 = 0 := by unfold T; rw [mul_pow, hK, zero_mul]
  have hU : IsUnit e := ⟨⟨e, e, by simpa only [pow_two] using he, by simpa only [pow_two] using he⟩, rfl⟩
  have hQ : f (a * e) ≠ 0 := ((hA.mul hU).map f).ne_zero
  have hBase (z : ZMod p) :
      ZMod.stdAddChar (a * ((e + T z) + (e + T z)⁻¹)) =
        ZMod.stdAddChar ((2 : ZMod M) * a * e) * ZMod.stdAddChar (f (a * e) * z ^ 2) := by
    have hInv := quadratic_nilpotent_inverse he (hT z)
    rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hInv]
    have hArg : a * ((e + T z) + (e - T z + e * T z ^ 2)) =
        (2 : ZMod M) * a * e + ((k * k : ℕ) : ZMod M) * (a * e) * ((z.val ^ 2 : ℕ) : ZMod M) := by
      unfold T
      push_cast
      ring
    rw [hArg, AddChar.map_add_eq_mul, stdAddChar_high_digit_nat]
    change _ = ZMod.stdAddChar ((2 : ZMod M) * a * e) * ZMod.stdAddChar (f (a * e) * z ^ 2)
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  have hSum : (∑ z : ZMod p, ZMod.stdAddChar (a * ((e + T z) + (e + T z)⁻¹))) =
      ZMod.stdAddChar ((2 : ZMod M) * a * e) *
        (primeQuadraticChar p (f (a * e)) * gaussSum (primeQuadraticChar p) ZMod.stdAddChar) := by
    simp_rw [hBase, ← Finset.mul_sum, prime_quadratic_sum hp (ZMod.isPrimitive_stdAddChar p) hQ]
  change ‖∑ z : ZMod p, ZMod.stdAddChar (a * ((e + T z) + (e + T z)⁻¹))‖ = _
  rw [hSum, norm_mul, norm_mul, norm_stdAddChar, norm_primeQuadraticChar hQ, one_mul, one_mul,
    norm_gaussSum_prime hp (ZMod.isPrimitive_stdAddChar p)]

end
end ManuscriptAudit.Paper8OddPrimePowerGaussBranch

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddPrimePowerGaussBranch.norm_odd_prime_power_branch
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
