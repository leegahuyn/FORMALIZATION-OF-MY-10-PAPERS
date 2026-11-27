import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Positive real-nome estimate for the actual Appell numerator at u = −1/2 and v = 0. -/

namespace ManuscriptAudit.Paper8AppellRealModel

noncomputable section

def term (r : ℝ) (n : ℤ) : ℝ := (-1 : ℝ) ^ n * r ^ (n ^ 2 + n) / (1 + r ^ (2 * n))

theorem term_reflection {r : ℝ} (hr : 0 < r) (n : ℤ) : term r (-n) = term r n := by
  have hExponent : (-n) ^ 2 + -n = (n ^ 2 + n) - 2 * n := by ring
  have hSign : (-1 : ℝ) ^ (-n) = (-1 : ℝ) ^ n := by
    rw [zpow_neg, ← inv_zpow] <;> norm_num
  have hPow : r ^ ((2 : ℤ) * n) ≠ 0 := zpow_ne_zero _ hr.ne'
  have hDivisor : 1 + r ^ ((2 : ℤ) * n) ≠ 0 := by positivity
  have hOther : 1 + (r ^ ((2 : ℤ) * n))⁻¹ ≠ 0 := by positivity
  unfold term
  rw [hSign, hExponent, zpow_sub₀ hr.ne', mul_neg, zpow_neg]
  field_simp [hPow, hDivisor, hOther] <;> ring

private theorem twice_le_square_add (n : ℕ) : 2 * n ≤ n ^ 2 + n := by
  cases n with
  | zero => decide
  | succ n =>
      have h := Nat.mul_le_mul_left (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      simpa only [mul_one, two_mul, pow_two] using Nat.add_le_add_right h (n + 1)

theorem norm_nat_term_le {r : ℝ} (hr : 0 < r) (h₁ : r ≤ 1) (n : ℕ) :
    ‖term r (n : ℤ)‖ ≤ (r ^ 2) ^ n := by
  have hExp : (n : ℤ) ^ 2 + (n : ℤ) = ((n ^ 2 + n : ℕ) : ℤ) := by push_cast <;> rfl
  have hDen : (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) := by push_cast <;> rfl
  simp only [term, hExp, hDen, zpow_natCast, Real.norm_eq_abs, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hr.le]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 + r ^ (2 * n))]
  calc
    _ ≤ r ^ (n ^ 2 + n) :=
      div_le_self (pow_nonneg hr.le _) (le_add_of_nonneg_right (pow_nonneg hr.le _))
    _ ≤ r ^ (2 * n) := pow_le_pow_of_le_one hr.le h₁ (twice_le_square_add n)
    _ = _ := by rw [pow_mul]

private theorem nat_abs_summable {r : ℝ} (hr : 0 < r) (h₁ : r < 1) :
    Summable (fun n : ℕ => ‖term r (n : ℤ)‖) := by
  have hR : r ^ 2 ≤ r := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left h₁.le hr.le
  have hSq : r ^ 2 < 1 := hR.trans_lt h₁
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_nat_term_le hr h₁.le)
    (summable_geometric_of_lt_one (sq_nonneg r) hSq)

theorem abs_summable {r : ℝ} (hr : 0 < r) (h₁ : r < 1) :
    Summable (fun n : ℤ => ‖term r n‖) := by
  apply Summable.of_nat_of_neg (nat_abs_summable hr h₁)
  simp only [term_reflection hr]
  exact nat_abs_summable hr h₁

private theorem tail_abs_le :
    |∑' n : ℕ, term (1 / 4) ((n + 1 : ℕ) : ℤ)| ≤ 1 / 15 := by
  have hn := nat_abs_summable (r := 1 / 4) (by norm_num) (by norm_num)
  have ht : Summable (fun n : ℕ => ‖term (1 / 4) ((n + 1 : ℕ) : ℤ)‖) :=
    hn.comp_injective Nat.succ_injective
  have hGeom : Summable (fun n : ℕ => (1 / 16 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_lt_one (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num)).mul_left (1 / 16)
  have hTsum : (∑' n : ℕ, (1 / 16 : ℝ) ^ (n + 1)) = 1 / 15 := by
    simp only [pow_succ', tsum_mul_left]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc
    _ ≤ ∑' n : ℕ, ‖term (1 / 4) ((n + 1 : ℕ) : ℤ)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm ht
    _ ≤ ∑' n : ℕ, (1 / 16 : ℝ) ^ (n + 1) :=
      ht.tsum_le_tsum (fun n => by
        have h := norm_nat_term_le (r := 1 / 4) (by norm_num) (by norm_num) (n + 1)
        norm_num at h ⊢
        exact h) hGeom
    _ = _ := hTsum

theorem tsum_quarter_pos : 0 < ∑' n : ℤ, term (1 / 4) n := by
  have hp : (0 : ℝ) < 1 / 4 := by norm_num
  have hNat := (nat_abs_summable hp (by norm_num)).of_norm
  have hNeg : (fun n : ℕ => term (1 / 4) (-(n : ℤ))) = fun n : ℕ => term (1 / 4) (n : ℤ) :=
    funext fun n => term_reflection hp (n : ℤ)
  have hNegSum := hNeg.symm ▸ hNat
  have hWhole := hNat.tsum_of_nat_of_neg hNegSum
  have hZero : term (1 / 4) 0 = 1 / 2 := by norm_num [term]
  simp only [hNeg, hNat.tsum_eq_zero_add, Nat.cast_zero, hZero] at hWhole
  rw [hWhole]
  linarith [(abs_le.mp tail_abs_le).1]

end
end ManuscriptAudit.Paper8AppellRealModel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8AppellRealModel.term_reflection,
      ``ManuscriptAudit.Paper8AppellRealModel.norm_nat_term_le,
      ``ManuscriptAudit.Paper8AppellRealModel.abs_summable,
      ``ManuscriptAudit.Paper8AppellRealModel.tsum_quarter_pos] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
