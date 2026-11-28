import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Coprime.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindOddPhase

/-! Exact arithmetic phase congruences for both odd-modulus branches at the prime 3. -/

namespace ManuscriptAudit.Paper8DedekindOddPhaseCRT

open Paper8DedekindKloostermanCongruence Paper8DedekindOddPhase

theorem phase_odd_baseline_mod_eight {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1) (hC : h.Coprime k) :
    (8 : ℤ) ∣ dedekindPhaseNumerator h k - dedekindPhaseNumerator 1 k -
      2 * (jacobiSym (h : ℤ) k - 1) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).1
  push_cast
  rw [phase_mod_eight_jacobi hh hk hC,
    phase_mod_eight_jacobi (by decide : 1 % 2 = 1) hk (Nat.coprime_one_left k)]
  simp only [Int.cast_one, jacobiSym.one_left]
  ring

theorem phase_odd_baseline_mod_twentyFour {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (h3 : ¬ (3 : ℕ) ∣ k) (hC : h.Coprime k) :
    (24 : ℤ) ∣ dedekindPhaseNumerator h k - dedekindPhaseNumerator 1 k -
      6 * (jacobiSym (h : ℤ) k - 1) := by
  have hk0 : 0 < k := by omega
  let c := jacobiSym (h : ℤ) k - 1
  let t := dedekindPhaseNumerator h k - dedekindPhaseNumerator 1 k
  have h8 : (8 : ℤ) ∣ t - 2 * c := phase_odd_baseline_mod_eight hh hk hC
  have h3t : (3 : ℤ) ∣ t := dvd_sub ((dedekind_phase_numerator_spec hk0 hC).2.2.2 h3)
    ((dedekind_phase_numerator_spec hk0 (Nat.coprime_one_left k)).2.2.2 h3)
  have hc : (2 : ℤ) ∣ c := by
    have hG : (h : ℤ).gcd k = 1 := by simpa only [Int.gcd_natCast_natCast] using hC.gcd_eq_one
    rcases jacobiSym.eq_one_or_neg_one hG with hSign | hSign
    · dsimp only [c]
      rw [hSign, sub_self]
      exact dvd_zero _
    · dsimp only [c]
      rw [hSign]
      decide
  have hCorr : (8 : ℤ) ∣ 4 * c := by
    obtain ⟨j, hj⟩ := hc
    refine ⟨j, ?_⟩
    rw [hj]
    ring
  have h8' : (8 : ℤ) ∣ t - 6 * c := by
    convert dvd_sub h8 hCorr using 1 <;> ring
  have h3' : (3 : ℤ) ∣ t - 6 * c := dvd_sub h3t ⟨2 * c, by ring⟩
  have hCop : IsCoprime (3 : ℤ) 8 := ⟨3, -1, by norm_num⟩
  simpa only [show (3 : ℤ) * 8 = 24 by norm_num] using hCop.mul_dvd h3' h8'

theorem phase_numerator_congr_mod_three_mul {h k : ℕ} (hk : 0 < k) (h3 : (3 : ℕ) ∣ k)
    (hC : h.Coprime k) (a : ℤ) (ha : (h : ZMod (3 * k)) * (a : ZMod (3 * k)) = 1) :
    (dedekindPhaseNumerator h k : ZMod (3 * k)) = (h : ZMod (3 * k)) + (a : ZMod (3 * k)) := by
  have hd := (dedekind_phase_numerator_spec hk hC).2.2.1 h3
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((h : ℤ) * dedekindPhaseNumerator h k - (1 + (h : ℤ) ^ 2)) (3 * k)).2 (by push_cast; exact hd)
  push_cast at hz
  have hN := sub_eq_zero.mp hz
  calc
    _ = (a : ZMod (3 * k)) * ((h : ZMod (3 * k)) * (dedekindPhaseNumerator h k : ZMod (3 * k))) := by
      rw [← mul_assoc, mul_comm (a : ZMod (3 * k)), ha, one_mul]
    _ = _ := by
      rw [hN, mul_add, mul_one, pow_two, ← mul_assoc, mul_comm (a : ZMod (3 * k)), ha, one_mul]
      exact add_comm _ _

end ManuscriptAudit.Paper8DedekindOddPhaseCRT

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindOddPhaseCRT.phase_odd_baseline_mod_twentyFour,
      ``ManuscriptAudit.Paper8DedekindOddPhaseCRT.phase_numerator_congr_mod_three_mul] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
