import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindResidueMoments

/-! The native integer Dedekind phase has its exact Kloosterman congruence modulo the denominator. -/

namespace ManuscriptAudit.Paper8DedekindKloostermanCongruence

open Finset Paper8ContourResidueWeights Paper8DedekindResidueMoments

noncomputable section

private theorem six_square_moment (k : ℕ) :
    6 * (∑ j : Fin k, (j.val : ℤ) ^ 2) = (k : ℤ) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    linear_combination ih

def dedekindPhaseNumerator (h k : ℕ) : ℤ :=
  2 * (h : ℤ) * (((k : ℤ) - 1) * (2 * (k : ℤ) - 1)) -
    12 * (∑ j : Fin k, (j.val : ℤ) * ((((h * j.val) / k : ℕ) : ℤ))) -
    3 * (k : ℤ) * ((k : ℤ) - 1)

theorem dedekind_phase_numerator_spec {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) :
    ((dedekindPhaseNumerator h k : ℤ) : ℚ) = 12 * (k : ℚ) * dedekindSum (h : ℤ) k ∧
      ((dedekindPhaseNumerator h k : ℤ) : ZMod k) =
        (h : ZMod k) + (((ZMod.unitOfCoprime h hC)⁻¹ : (ZMod k)ˣ) : ZMod k) ∧
      ((3 : ℕ) ∣ k → (3 * (k : ℤ)) ∣ (h : ℤ) * dedekindPhaseNumerator h k - (1 + (h : ℤ) ^ 2)) ∧
      (¬ (3 : ℕ) ∣ k → (3 : ℤ) ∣ dedekindPhaseNumerator h k) := by
  let e := residuePerm h k hk hC
  let jv (j : Fin k) : ℤ := j.val
  let r (j : Fin k) : ℤ := (e j).val
  let q (j : Fin k) : ℤ := (((h * j.val) / k : ℕ) : ℤ)
  let J : ℤ := ∑ j : Fin k, jv j ^ 2
  let S : ℤ := ∑ j : Fin k, jv j * r j
  let Q : ℤ := ∑ j : Fin k, jv j * q j
  let R : ℤ := ∑ j : Fin k, q j ^ 2
  let L : ℤ := ((k : ℤ) - 1) * (2 * (k : ℤ) - 1)
  let P : ℤ := 2 * (h : ℤ) * L - 12 * Q
  let N : ℤ := P - 3 * (k : ℤ) * ((k : ℤ) - 1)
  let u := ZMod.unitOfCoprime h hC
  have hK : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hJ : 6 * J = (k : ℤ) * L := by
    have hh := six_square_moment k
    change _ = _
    dsimp only [J, jv, L]
    convert hh using 1 <;> ring
  have hDiv (j : Fin k) : r j + (k : ℤ) * q j = (h : ℤ) * jv j := by
    have hh := Nat.mod_add_div (h * j.val) k
    dsimp only [r, q, e, jv]
    rw [residuePerm_val]
    exact_mod_cast hh
  have hS : S = (h : ℤ) * J - (k : ℤ) * Q := by
    calc
      _ = ∑ j : Fin k, ((h : ℤ) * jv j ^ 2 - (k : ℤ) * (jv j * q j)) := by
        apply Finset.sum_congr rfl
        intro j _
        linear_combination jv j * hDiv j
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hR : (∑ j : Fin k, r j ^ 2) = J :=
    Fintype.sum_equiv e _ _ (fun j => rfl)
  have hP : (2 * (h : ℤ)) * S =
      (1 + (h : ℤ) ^ 2) * J - (k : ℤ) ^ 2 * R := by
    have hPoint (j : Fin k) : (2 * (h : ℤ)) * (jv j * r j) =
        r j ^ 2 + (h : ℤ) ^ 2 * jv j ^ 2 - (k : ℤ) ^ 2 * q j ^ 2 := by
      have hh : r j - (h : ℤ) * jv j = -(k : ℤ) * q j := by linear_combination hDiv j
      have hh2 := congrArg (fun a : ℤ => a ^ 2) hh
      change (r j - (h : ℤ) * jv j) ^ 2 = (-(k : ℤ) * q j) ^ 2 at hh2
      linear_combination -hh2
    calc
      _ = ∑ j : Fin k, (2 * (h : ℤ)) * (jv j * r j) := by unfold S; rw [Finset.mul_sum]
      _ = ∑ j : Fin k, (r j ^ 2 + (h : ℤ) ^ 2 * jv j ^ 2 - (k : ℤ) ^ 2 * q j ^ 2) := by
        exact Finset.sum_congr rfl (fun j _ => hPoint j)
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hR]
        change J + (h : ℤ) ^ 2 * J - (k : ℤ) ^ 2 * R = _
        ring
  have hKP : (k : ℤ) * P = 12 * S := by
    unfold P
    linear_combination -12 * hS - 2 * (h : ℤ) * hJ
  have hCong : (h : ℤ) * P = (1 + (h : ℤ) ^ 2) * L - 6 * (k : ℤ) * R := by
    apply mul_left_cancel₀ hK
    calc
      _ = (h : ℤ) * ((k : ℤ) * P) := by ring
      _ = (1 + (h : ℤ) ^ 2) * (6 * J) - 6 * (k : ℤ) ^ 2 * R := by
        rw [hKP]
        linear_combination 6 * hP
      _ = _ := by rw [hJ]; ring
  have hPN : (N : ZMod k) = (P : ZMod k) := by
    dsimp only [N]
    push_cast
    simp
  have hCast := congrArg (fun n : ℤ => (n : ZMod k)) hCong
  change (((h : ℤ) * P : ℤ) : ZMod k) =
    (((1 + (h : ℤ) ^ 2) * L - 6 * (k : ℤ) * R : ℤ) : ZMod k) at hCast
  dsimp only [L] at hCast
  push_cast at hCast
  simp only [ZMod.natCast_self, mul_zero, zero_mul, zero_sub, neg_mul_neg, one_mul, mul_one, sub_zero] at hCast
  have hUnit : (u : ZMod k) * (N : ZMod k) = 1 + (u : ZMod k) ^ 2 := by
    rw [hPN]
    exact hCast
  have hZ : (N : ZMod k) = (h : ZMod k) + ((u⁻¹ : (ZMod k)ˣ) : ZMod k) := by
    calc
      _ = ((u⁻¹ : (ZMod k)ˣ) : ZMod k) * ((u : ZMod k) * (N : ZMod k)) := by
        rw [Units.inv_mul_cancel_left]
      _ = _ := by
        rw [hUnit, mul_add, mul_one, pow_two, Units.inv_mul_cancel_left]
        exact add_comm _ _
  have hKQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hSq : (∑ j : Fin k, fraction j * fraction (e j)) = (S : ℚ) / (k : ℚ) ^ 2 := by
    unfold S
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    unfold fraction jv r
    simp only [Int.cast_natCast] 
    ring
  have hKPq := congrArg (fun n : ℤ => (n : ℚ)) hKP
  push_cast at hKPq
  have hPF : (P : ℚ) = (12 * (S : ℚ)) / (k : ℚ) :=
    (eq_div_iff hKQ).2 (by simpa only [mul_comm] using hKPq)
  have hRat : (N : ℚ) = 12 * (k : ℚ) * dedekindSum (h : ℤ) k := by
    rw [dedekindSum_eq_fraction_product hk hC]
    change (N : ℚ) = 12 * (k : ℚ) * ((∑ j : Fin k, fraction j * fraction (e j)) - ((k : ℚ) - 1) / 4)
    rw [hSq]
    unfold N
    push_cast
    rw [hPF]
    field_simp [hKQ] <;> ring
  have hFact : (h : ℤ) * N - (1 + (h : ℤ) ^ 2) =
      (k : ℤ) * ((1 + (h : ℤ) ^ 2) * (2 * (k : ℤ) - 3) - 6 * R -
        3 * (h : ℤ) * ((k : ℤ) - 1)) := by
    unfold N
    dsimp only [L] at hCong
    linear_combination hCong
  have hThree (hk3 : (3 : ℕ) ∣ k) : (3 * (k : ℤ)) ∣ (h : ℤ) * N - (1 + (h : ℤ) ^ 2) := by
    obtain ⟨m, hm⟩ := hk3
    have hz : (k : ℤ) = 3 * (m : ℤ) := by exact_mod_cast hm
    refine ⟨(1 + (h : ℤ) ^ 2) * (2 * (m : ℤ) - 1) - 2 * R - (h : ℤ) * ((k : ℤ) - 1), ?_⟩
    rw [hFact]
    linear_combination (2 * (k : ℤ) * (1 + (h : ℤ) ^ 2)) * hz
  have hnThree (hk3 : ¬ (3 : ℕ) ∣ k) : (3 : ℤ) ∣ N := by
    have hEq : (k : ℤ) * N = 12 * S - 3 * (k : ℤ) ^ 2 * ((k : ℤ) - 1) := by
      unfold N
      linear_combination hKP
    have he := congrArg (fun z : ℤ => (z : ZMod 3)) hEq
    change (((k : ℤ) * N : ℤ) : ZMod 3) =
      ((12 * S - 3 * (k : ℤ) ^ 2 * ((k : ℤ) - 1) : ℤ) : ZMod 3) at he
    push_cast at he
    have he0 : (k : ZMod 3) * (N : ZMod 3) = 0 := by
      simpa only [show (12 : ZMod 3) = 0 by decide, show (3 : ZMod 3) = 0 by decide,
        zero_mul, sub_zero] using he
    have hk0 : (k : ZMod 3) ≠ 0 := fun h0 => hk3 ((ZMod.natCast_eq_zero_iff k 3).1 h0)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd N 3).1 ((mul_eq_zero.mp he0).resolve_left hk0)
  exact ⟨hRat, hZ, hThree, hnThree⟩

theorem dedekind_integer_phase_congruence {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) :
    ∃ N : ℤ, (N : ℚ) = 12 * (k : ℚ) * dedekindSum (h : ℤ) k ∧
      (N : ZMod k) = (h : ZMod k) + (((ZMod.unitOfCoprime h hC)⁻¹ : (ZMod k)ˣ) : ZMod k) := by
  obtain ⟨hv, hm, _, _⟩ := dedekind_phase_numerator_spec hk hC
  exact ⟨_, hv, hm⟩

end
end ManuscriptAudit.Paper8DedekindKloostermanCongruence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindKloostermanCongruence.dedekind_integer_phase_congruence
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
