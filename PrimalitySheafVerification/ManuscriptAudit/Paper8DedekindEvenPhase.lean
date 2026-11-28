import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindOddPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindReciprocity
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspPhase

/-! The exact two-primary Dedekind phase for an even denominator follows from native reciprocity. -/

namespace ManuscriptAudit.Paper8DedekindEvenPhase

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence Paper8DedekindOddPhase
open Paper8DedekindReciprocity Paper8OddCrossCuspPhase

private theorem phase_numerator_reciprocity {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) :
    (h : ℤ) * dedekindPhaseNumerator h k + (k : ℤ) * dedekindPhaseNumerator k h =
      (h : ℤ) ^ 2 + (k : ℤ) ^ 2 - 3 * (h : ℤ) * (k : ℤ) + 1 := by
  have hH := (dedekind_phase_numerator_spec hk hC).1
  have hK := (dedekind_phase_numerator_spec hh hC.symm).1
  apply (Int.cast_injective (α := ℚ))
  push_cast
  rw [hH, hK]
  linear_combination dedekindSum_reciprocity_scaled hh hk hC

private theorem phase_numerator_translate_once {a b : ℕ} (hb : 0 < b) (hC : a.Coprime b) :
    dedekindPhaseNumerator (a + b) b = dedekindPhaseNumerator a b := by
  have hC' : (a + b).Coprime b := by
    simpa only [one_mul] using (Nat.coprime_add_mul_right_left a b 1).2 hC
  have hD : dedekindSum (((a + b : ℕ)) : ℤ) b = dedekindSum (a : ℤ) b := by
    push_cast
    simpa only [mul_one] using dedekind_translate hb (a : ℤ) 1
  apply (Int.cast_injective (α := ℚ))
  rw [(dedekind_phase_numerator_spec hb hC').1, (dedekind_phase_numerator_spec hb hC).1, hD]

theorem phase_even_numerator_two_part {h k t : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 0)
    (hk0 : 0 < k) (hC : h.Coprime k) (ht : t ∣ k) (a : ℤ)
    (ha : (h : ZMod (8 * t)) * (a : ZMod (8 * t)) = 1) :
    (dedekindPhaseNumerator h k : ZMod (8 * t)) =
      (1 - (k : ZMod (8 * t))) * (h : ZMod (8 * t)) +
        ((k : ZMod (8 * t)) ^ 2 + 1) * (a : ZMod (8 * t)) -
        2 * (k : ZMod (8 * t)) * (a : ZMod (8 * t)) * (jacobiSym (k : ℤ) h : ZMod (8 * t)) := by
  have hh0 : 0 < h := by omega
  have hOdd : (k + h) % 2 = 1 := by omega
  let N := dedekindPhaseNumerator h k
  let N' := dedekindPhaseNumerator k h
  let J := jacobiSym (k : ℤ) h
  let B := (h : ℤ) ^ 2 - 3 * (h : ℤ) + 2 * J
  have hC' : (k + h).Coprime h := by
    simpa only [one_mul] using (Nat.coprime_add_mul_right_left k h 1).2 hC.symm
  have hJ : jacobiSym (((k + h : ℕ)) : ℤ) h = J := by
    apply jacobiSym.mod_left'
    apply (ZMod.intCast_eq_intCast_iff' _ _ h).1
    push_cast
    rw [ZMod.natCast_self, add_zero]
  have h8 : (8 : ℤ) ∣ N' - B := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).1
    have hR := phase_mod_eight_jacobi hOdd hh hC'
    rw [phase_numerator_translate_once hh0 hC.symm, hJ] at hR
    unfold B N'
    push_cast
    rw [hR]
    ring
  have hT : ((8 * t : ℕ) : ℤ) ∣ (k : ℤ) * (N' - B) := by
    obtain ⟨w, hw⟩ := ht
    obtain ⟨q, hq⟩ := h8
    have hwZ := congrArg (fun x : ℕ => (x : ℤ)) hw
    push_cast at hwZ ⊢
    refine ⟨w * q, ?_⟩
    rw [hwZ, hq]
    ring
  let M := 8 * t
  have hTz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 hT
  push_cast at hTz
  have hK : (k : ZMod M) * (N' : ZMod M) = (k : ZMod M) * (B : ZMod M) := by
    rw [mul_sub] at hTz
    exact sub_eq_zero.mp hTz
  have hRec := congrArg (fun x : ℤ => (x : ZMod M)) (phase_numerator_reciprocity hh0 hk0 hC)
  push_cast at hRec
  have hR : (h : ZMod M) * (N : ZMod M) =
      (h : ZMod M) ^ 2 + (k : ZMod M) ^ 2 - 3 * (h : ZMod M) * (k : ZMod M) + 1 -
        (k : ZMod M) * (B : ZMod M) := by
    change (h : ZMod M) * (N : ZMod M) + (k : ZMod M) * (N' : ZMod M) =
      (h : ZMod M) ^ 2 + (k : ZMod M) ^ 2 - 3 * (h : ZMod M) * (k : ZMod M) + 1 at hRec
    linear_combination hRec - hK
  calc
    _ = (a : ZMod M) * ((h : ZMod M) * (N : ZMod M)) := by
      rw [← mul_assoc, mul_comm (a : ZMod M), ha, one_mul]
    _ = ((a : ZMod M) * (h : ZMod M)) * ((1 - (k : ZMod M)) * (h : ZMod M)) +
        ((k : ZMod M) ^ 2 + 1) * (a : ZMod M) -
        2 * (k : ZMod M) * (a : ZMod M) * (J : ZMod M) := by
      rw [hR]
      unfold B
      push_cast
      ring
    _ = _ := by rw [mul_comm (a : ZMod M), ha, one_mul]

end ManuscriptAudit.Paper8DedekindEvenPhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenPhase.phase_even_numerator_two_part
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
