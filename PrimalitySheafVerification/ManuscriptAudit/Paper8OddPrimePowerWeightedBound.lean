import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddPrimePowerLift

/-! Square-root cancellation of the two stationary branches at odd prime powers with odd exponent. -/

namespace ManuscriptAudit.Paper8OddPrimePowerWeightedBound

open Finset Paper8PrimePowerStationaryPhase Paper8ZModDigitOrthogonality Paper8ProductStationaryPhase
open Paper8PrimePowerDigitSum Paper8OddPrimePowerLift
open scoped Classical

noncomputable section

theorem norm_weighted_symmetric_sum_odd_prime_power {p r : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hr : 0 < r) (w : ZMod p → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (a : ZMod (p ^ r * (p * p ^ r))) (ha : IsUnit a) :
    letI : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    ‖weightedSymmetricUnitSum (fun x : ZMod (p * p ^ r) => w (reduceHighDigit x : ZMod p)) a‖ ≤
      2 * ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
  let k := p ^ r
  let m := p * k
  let M := k * m
  let P : Nat.Prime p := Fact.out
  have hk : 0 < k := pow_pos P.pos _
  have hk1 : 1 < k := Nat.one_lt_pow hr.ne' P.one_lt
  letI : NeZero p := ⟨P.ne_zero⟩
  letI : NeZero k := ⟨hk.ne'⟩
  have hpk : p ∣ k := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    refine ⟨p ^ j, ?_⟩
    unfold k
    rw [hj, pow_succ, mul_comm]
  have hkm : k ∣ m := dvd_mul_left k p
  let B (c : ZMod k) (z : ZMod p) : ZMod m := ((c.val + k * z.val : ℕ) : ZMod m)
  let X (b : ZMod m) : ZMod M := (b.val : ZMod M)
  let W (b : ZMod m) := w (reduceHighDigit b : ZMod p)
  have hLow (b : ZMod m) : reduceLowDigit (X b) = b := by
    unfold X
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hRed (c : ZMod k) (z : ZMod p) : (reduceHighDigit (X (B c z)) : ZMod k) = c := by
    have h := reduceLowDigit_apply (n := p) (m := k) (B c z)
    have hM₁ : (reduceHighDigit (X (B c z)) : ZMod k) = (B c z).val := by
      unfold X
      rw [map_natCast]
    rw [hM₁, ← h]
    unfold B
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  have hWeight (c : ZMod k) (z : ZMod p) : W (B c z) = w (c.val : ZMod p) := by
    unfold W B
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, (ZMod.natCast_eq_zero_iff k p).2 hpk, zero_mul, add_zero]
  have hU (c : ZMod k) (z : ZMod p) (hc : c ^ 2 = 1) : IsUnit (X (B c z)) := by
    have hcU : IsUnit c := ⟨⟨c, c, by simpa only [pow_two] using hc, by simpa only [pow_two] using hc⟩, rfl⟩
    have hCast : ((B c z).val : ZMod k) = c := by simpa only [X, map_natCast] using hRed c z
    have hC : IsUnit ((B c z).val : ZMod (p ^ r)) := by change IsUnit ((B c z).val : ZMod k); rw [hCast]; exact hcU
    have hM : M = p ^ (r + (1 + r)) := by unfold M m k; rw [pow_add, pow_add, pow_one]
    unfold X
    rw [hM, ZMod.isUnit_natCast_iff_not_dvd_pow P (by omega)]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow P hr).1 hC
  let T (c : ZMod k) := ∑ z : ZMod p, symmetricPhase a (X (B c z))
  have hNormModel (c : ZMod k) (e : ℤ) (s : ℕ)
      (hE : (e : ZMod M) ^ 2 = 1) (hC : (c.val : ℤ) = e + (k : ℤ) * (s : ℤ)) :
      ‖T c‖ = Real.sqrt (p : ℝ) := by
    let F (z : ZMod p) := symmetricPhase a ((e : ZMod M) + (k : ZMod M) * (z.val : ZMod M))
    have hRow (z : ZMod p) : symmetricPhase a (X (B c z)) = F (z + (s : ZMod p)) := by
      apply stationary_lift_phase_at_sign hpk a (e : ZMod M) (X (B c z)) hE (z + (s : ZMod p))
      rw [hLow, map_add, map_mul, map_intCast, map_natCast, map_natCast, lowDigit_mul_shift]
      unfold B
      push_cast
      have h := congrArg (fun x : ℤ => (x : ZMod m)) hC
      push_cast at h
      rw [h]
      ring
    let shift : ZMod p ≃ ZMod p :=
      { toFun := fun z => z + (s : ZMod p)
        invFun := fun z => z - (s : ZMod p)
        left_inv := fun z => by simp
        right_inv := fun z => by simp }
    have hRe : (∑ z : ZMod p, F (z + (s : ZMod p))) = ∑ z : ZMod p, F z :=
      Fintype.sum_equiv shift _ _ (fun _ => rfl)
    have hM : M = p * (p ^ r * p ^ r) := by unfold M m k; ring
    unfold T
    simp_rw [hRow]
    rw [hRe]
    exact norm_odd_branch_modulus_congr hM hp hr a (e : ZMod M) ha hE
  have hNorm (c : ZMod k) (hc : c ^ 2 = 1) : ‖T c‖ = Real.sqrt (p : ℝ) := by
    rcases (prime_pow_sq_eq_one_iff P hp c).1 hc with he | he
    · have hv : c.val = 1 := by rw [he, ZMod.val_one'' hk1.ne']
      apply hNormModel c 1 0 (by simp)
      rw [hv]
      simp
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      have hv : c.val = j := by rw [he]; exact (by simpa only [hj] using ZMod.val_neg_one j)
      apply hNormModel c (-1) 1 (by simp)
      rw [hv, hj]
      push_cast
      ring
  let U := Finset.univ.filter (fun c : ZMod k => c ^ 2 = 1)
  have hSubset : U ⊆ ({1, -1} : Finset (ZMod k)) := by
    intro c hc
    have hRoot := (prime_pow_sq_eq_one_iff P hp c).1 (Finset.mem_filter.mp hc).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hRoot
  have hCard : U.card ≤ 2 :=
    (Finset.card_le_card hSubset).trans (by
      calc
        _ ≤ ({(-1 : ZMod k)} : Finset (ZMod k)).card + 1 := Finset.card_insert_le _ _
        _ = _ := by simp)
  change ‖weightedSymmetricUnitSum W a‖ ≤ 2 * (k : ℝ) * Real.sqrt (p : ℝ)
  rw [weighted_symmetric_sum_stationary hkm W a ha]
  let Q (b : ZMod m) := if IsUnit (X b) ∧ (reduceHighDigit (X b) : ZMod k) ^ 2 = 1 then
    W b * symmetricPhase a (X b) else 0
  change ‖(k : ℂ) * (∑ b : ZMod m, Q b)‖ ≤ _
  have hQ : (∑ b : ZMod m, Q b) =
      ∑ c : ZMod k, if c ^ 2 = 1 then w (c.val : ZMod p) * T c else 0 := by
    rw [sum_residue_digits, Finset.sum_comm]
    change (∑ c : ZMod k, ∑ z : ZMod p, Q (B c z)) = _
    apply Finset.sum_congr rfl
    intro c _
    unfold Q
    simp_rw [hRed, hWeight]
    by_cases hc : c ^ 2 = 1
    · have hAll (z : ZMod p) : IsUnit (X (B c z)) := hU c z hc
      simp only [hc, and_true, hAll, if_true]
      unfold T
      rw [Finset.mul_sum]
    · simp [hc]
  rw [hQ, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (k : ℝ) * ∑ c : ZMod k, ‖if c ^ 2 = 1 then w (c.val : ZMod p) * T c else 0‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) * ∑ c : ZMod k, if c ^ 2 = 1 then Real.sqrt (p : ℝ) else 0 := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) (Nat.cast_nonneg _)
      by_cases hc : c ^ 2 = 1
      · rw [if_pos hc, if_pos hc, norm_mul, hNorm c hc]
        exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (hw _)
      · simp [hc]
    _ = (k : ℝ) * ((U.card : ℝ) * Real.sqrt (p : ℝ)) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (2 * Real.sqrt (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hCard)
        (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by ring

end
end ManuscriptAudit.Paper8OddPrimePowerWeightedBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddPrimePowerWeightedBound.norm_weighted_symmetric_sum_odd_prime_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
