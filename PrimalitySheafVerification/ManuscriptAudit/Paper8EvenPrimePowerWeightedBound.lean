import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerDigitSum

/-! Square-root cancellation at even exponents with arbitrary bounded low-digit weights. -/

namespace ManuscriptAudit.Paper8EvenPrimePowerWeightedBound

open Finset Paper8PrimePowerStationaryPhase Paper8ProductStationaryPhase Paper8PrimePowerDigitSum
open Paper8ZModDigitOrthogonality
open scoped Classical

noncomputable section

theorem norm_weighted_symmetric_sum_even_prime_power {p r : ℕ}
    (P : p.Prime) (hp : p ≠ 2) (_hr : 0 < r)
    (w : ZMod (p ^ r) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (a : ZMod (p ^ r * p ^ r)) (ha : IsUnit a) :
    letI : NeZero (p ^ r) := ⟨pow_ne_zero _ P.ne_zero⟩
    ‖weightedSymmetricUnitSum w a‖ ≤ 2 * ((p ^ r : ℕ) : ℝ) := by
  let k := p ^ r
  have hk : 0 < k := pow_pos P.pos _
  letI : NeZero k := ⟨hk.ne'⟩
  let X (b : ZMod k) : ZMod (k * k) := (b.val : ZMod (k * k))
  have hX (b : ZMod k) : (reduceHighDigit (X b) : ZMod k) = b := by
    unfold X
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hChar (x : ZMod (k * k)) : ‖symmetricPhase a x‖ = 1 := by
    have hM : 0 < ringChar (ZMod (k * k)) := by
      rw [ZMod.ringChar_zmod_n]
      exact Nat.mul_pos hk hk
    unfold symmetricPhase
    have hU := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((ZMod.stdAddChar (N := k * k)).val_mem_rootsOfUnity (a * (x + x⁻¹)) hM)
    simpa only [IsUnit.unit_spec] using hU
  let U := Finset.univ.filter (fun b : ZMod k => b ^ 2 = 1)
  have hSubset : U ⊆ ({1, -1} : Finset (ZMod k)) := by
    intro b hb
    have hRoot := (prime_pow_sq_eq_one_iff P hp b).1 (Finset.mem_filter.mp hb).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hRoot
  have hCard : U.card ≤ 2 :=
    (Finset.card_le_card hSubset).trans (by
      calc
        _ ≤ ({(-1 : ZMod k)} : Finset (ZMod k)).card + 1 := Finset.card_insert_le _ _
        _ = _ := by simp)
  change ‖weightedSymmetricUnitSum w a‖ ≤ 2 * (k : ℝ)
  rw [weighted_symmetric_sum_stationary (dvd_refl k) w a ha]
  let Q (b : ZMod k) := if IsUnit (X b) ∧ (reduceHighDigit (X b) : ZMod k) ^ 2 = 1 then
    w b * symmetricPhase a (X b) else 0
  change ‖(k : ℂ) * (∑ b : ZMod k, Q b)‖ ≤ _
  have hPoint (b : ZMod k) : ‖Q b‖ ≤ if b ^ 2 = 1 then 1 else 0 := by
    unfold Q
    rw [hX]
    by_cases hb : b ^ 2 = 1
    · rw [if_pos hb]
      by_cases hu : IsUnit (X b)
      · rw [if_pos (And.intro hu hb), norm_mul, hChar, mul_one]
        exact hw b
      · rw [if_neg (fun h => hu h.1), norm_zero]
        norm_num
    · simp [hb]
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (k : ℝ) * ∑ b : ZMod k, ‖Q b‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) * ∑ b : ZMod k, if b ^ 2 = 1 then (1 : ℝ) else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hPoint b)) (Nat.cast_nonneg _)
    _ = (k : ℝ) * (U.card : ℝ) := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (k : ℝ) * 2 := mul_le_mul_of_nonneg_left (by exact_mod_cast hCard) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

end
end ManuscriptAudit.Paper8EvenPrimePowerWeightedBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EvenPrimePowerWeightedBound.norm_weighted_symmetric_sum_even_prime_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
