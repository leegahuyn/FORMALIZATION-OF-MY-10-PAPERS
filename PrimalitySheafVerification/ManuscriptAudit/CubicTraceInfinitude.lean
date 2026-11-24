import PrimalitySheafVerification.ManuscriptAudit.CubicTrace
import Mathlib.Data.Nat.Factorial.Basic

namespace PrimalitySheafVerification.ManuscriptAudit

private theorem paper5_exists_residue_prime_dvd (n : ℕ) (hn : n % 3 = 2) :
    ∃ q : ℕ, q.Prime ∧ q % 3 = 2 ∧ q ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    let q := n.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega : n ≠ 1)
    have hqn : q ∣ n := Nat.minFac_dvd n
    by_cases hq2 : q % 3 = 2
    · exact ⟨q, hq, hq2, hqn⟩
    · obtain ⟨m, hnm⟩ := hqn
      have hprod : ((q % 3) * (m % 3)) % 3 = 2 :=
        (Nat.mul_mod q m 3).symm.trans (by rw [← hnm, hn])
      have hq1 : q % 3 = 1 := by
        have hb : q % 3 < 3 := Nat.mod_lt _ (by decide)
        by_contra hq1
        have hq0 : q % 3 = 0 := by omega
        simp [hq0] at hprod
      have hm2 : m % 3 = 2 := by simpa [hq1] using hprod
      have hmul : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq.two_le
      have hlt : m < n := by omega
      obtain ⟨r, hr, hr2, hrm⟩ := ih m hlt hm2
      refine ⟨r, hr, hr2, ?_⟩
      rw [hnm]
      exact dvd_mul_of_dvd_right hrm q

private theorem paper5_exists_large_residue_prime (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q % 3 = 2 := by
  let n := 3 * B.factorial - 1
  have hf : 0 < B.factorial := Nat.factorial_pos B
  have hn : n % 3 = 2 := by
    dsimp [n]
    omega
  obtain ⟨q, hq, hq2, hqd⟩ := paper5_exists_residue_prime_dvd n hn
  refine ⟨q, ?_, hq, hq2⟩
  by_contra h
  have hle : q ≤ B := by omega
  have hqf : q ∣ B.factorial := Nat.dvd_factorial hq.pos hle
  have hqmul : q ∣ 3 * B.factorial := dvd_mul_of_dvd_right hqf 3
  have haux : 3 * B.factorial - n = 1 := by
    dsimp [n]
    omega
  exact hq.ne_one (Nat.dvd_one.mp (haux ▸ Nat.dvd_sub hqmul hqd))

/-- The varying-coefficient family has trace zero at arbitrarily large good primes
when the constant coefficient is a fixed nonzero integer. To apply this to the
geometric supersingularity claim in Paper 5, one also needs the comparison
from zero point-count trace to geometric supersingularity. -/
theorem paper5_arbitrarily_large_good_trace_zero (A : ℤ) (hA : A ≠ 0) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 3 = 2 ∧
      (paper5TraceCurve p (A : ZMod p)).Δ ≠ 0 ∧
      (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p (A : ZMod p)).toProjective.Point : ℤ) = 0 := by
  obtain ⟨p, hpB, hpp, hp3⟩ := paper5_exists_large_residue_prime (max N (max 5 A.natAbs))
  have hN : N < p := lt_of_le_of_lt (le_max_left _ _) hpB
  have hMax : max 5 A.natAbs < p := lt_of_le_of_lt (le_max_right _ _) hpB
  have hp5 : 5 ≤ p := (le_max_left 5 A.natAbs).trans hMax.le
  have hpA : A.natAbs < p := lt_of_le_of_lt (le_max_right 5 A.natAbs) hMax
  have hc : (A : ZMod p) ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd A p).1 hz
    have hd : p ∣ A.natAbs := ⟨k.natAbs, by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hk⟩
    exact (not_le_of_gt hpA) (Nat.le_of_dvd (Int.natAbs_pos.mpr hA) hd)
  letI : Fact p.Prime := ⟨hpp⟩
  exact ⟨p, hN, hpp, hp3, paper5_traceCurve_discriminant_ne_zero hp5 hc,
    paper5_traceCurve_trace_eq_zero hp5 hp3 hc⟩

open Lean Elab Command in
run_cmd do
  let name := ``paper5_arbitrarily_large_good_trace_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"

end PrimalitySheafVerification.ManuscriptAudit
