import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Normed
import PrimalitySheafVerification.ManuscriptAudit.ThetaQSeriesAnalytic
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrintedInsideSeries

/-!
# The two inside series as complex analytic functions

In the open unit disk both displayed expressions have genuine, locally
uniformly absolutely convergent sums. The estimate holds for both the doubled index and the squared product.
-/

namespace ManuscriptAudit.Paper8InsideComplexAnalytic

open Filter Set
open scoped Topology

noncomputable section

def pochhammer (q : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1 + q ^ (j + 1))

def printedTerm (n : ℕ) (q : ℂ) : ℂ := q ^ (n ^ 2) / pochhammer q (2 * n)

def standardTerm (n : ℕ) (q : ℂ) : ℂ := q ^ (n ^ 2) / pochhammer q n ^ 2

def printed (q : ℂ) : ℂ := ∑' n : ℕ, printedTerm n q

def standard (q : ℂ) : ℂ := ∑' n : ℕ, standardTerm n q

private theorem factor_lower {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r ≤ 1)
    (j : ℕ) : 1 - r ≤ ‖1 + q ^ (j + 1)‖ := by
  have hPow : ‖q ^ (j + 1)‖ ≤ r := by
    simpa only [pow_one] using
      ThetaQSeriesAnalytic.norm_power_le_radius (by omega : 1 ≤ j + 1) hr hqr
  have h := norm_sub_norm_le (1 : ℂ) (-(q ^ (j + 1)))
  rw [norm_one, norm_neg, sub_neg_eq_add] at h
  linarith only [h, hPow]

theorem pochhammer_lower {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r ≤ 1)
    (n : ℕ) : (1 - r) ^ n ≤ ‖pochhammer q n‖ := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
      rw [pochhammer, Finset.prod_range_succ, norm_mul, ← pochhammer, pow_succ]
      exact mul_le_mul ih (factor_lower hqr hr n) (sub_nonneg.mpr hr) (norm_nonneg _)

theorem pochhammer_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : pochhammer q n ≠ 0 := by
  exact norm_pos_iff.mp ((pow_pos (sub_pos.mpr hq) _).trans_le
    (pochhammer_lower le_rfl hq.le n))

private def majorant (r : ℝ) (n : ℕ) : ℝ :=
  r ^ (n ^ 2) * ((1 - r)⁻¹ ^ 2) ^ n

private theorem majorant_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ majorant r n := by
  unfold majorant
  positivity

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Summable (majorant r) := by
  let b : ℝ := (1 - r)⁻¹ ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hLim : Tendsto (fun n : ℕ => r ^ n * b) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr₁).mul_const b
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  filter_upwards [hLim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  rw [Real.norm_of_nonneg (majorant_nonneg hr _), Real.norm_of_nonneg (majorant_nonneg hr _)]
  change r ^ ((n + 1) ^ 2) * b ^ (n + 1) ≤ (1 / 2) * (r ^ (n ^ 2) * b ^ n)
  have hExp : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  rw [hExp, pow_add, pow_succ b]
  have hPower : r ^ (2 * n + 1) ≤ r ^ n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ 2 * n + 1)
    have hk' : r ^ k ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr hr₁.le k
    rw [hk, pow_add]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hk' (pow_nonneg hr n)
  calc
    _ = (r ^ (2 * n + 1) * b) * (r ^ (n ^ 2) * b ^ n) := by ring
    _ ≤ (r ^ n * b) * (r ^ (n ^ 2) * b ^ n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPower hb) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (by positivity)

private theorem norm_quotient_le_majorant {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1)
    (n : ℕ) {d : ℂ} (hd : (1 - r) ^ (2 * n) ≤ ‖d‖) :
    ‖q ^ (n ^ 2) / d‖ ≤ majorant r n := by
  have hD : 0 < (1 - r) ^ (2 * n) := pow_pos (sub_pos.mpr hr) _
  rw [norm_div, norm_pow]
  calc
    _ ≤ r ^ (n ^ 2) / (1 - r) ^ (2 * n) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hqr _) hD hd
    _ = majorant r n := by
      simp only [majorant, div_eq_mul_inv, inv_pow, pow_mul]

private theorem printed_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) (n : ℕ) :
    ‖printedTerm n q‖ ≤ majorant r n :=
  norm_quotient_le_majorant hqr hr n (pochhammer_lower hqr hr.le _)

private theorem standard_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) (n : ℕ) :
    ‖standardTerm n q‖ ≤ majorant r n := by
  refine norm_quotient_le_majorant hqr hr n ?_
  rw [norm_pow, Nat.mul_comm 2 n, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr hr.le) _) (pochhammer_lower hqr hr.le _) 2

private theorem pochhammer_differentiable (n : ℕ) :
    Differentiable ℂ (fun q => pochhammer q n) := by
  induction n with
  | zero => simpa [pochhammer] using differentiable_const (c := (1 : ℂ))
  | succ n ih =>
      rw [show (fun q => pochhammer q (n + 1)) =
          (fun q => pochhammer q n * (1 + q ^ (n + 1))) by
            funext q
            simp only [pochhammer, Finset.prod_range_succ]]
      exact ih.mul (by fun_prop)

private theorem analytic_on_unit_disk (term : ℕ → ℂ → ℂ)
    (hTerm : ∀ n, DifferentiableOn ℂ (term n) (Metric.ball (0 : ℂ) 1))
    (hBound : ∀ n {q : ℂ} {r : ℝ}, ‖q‖ ≤ r → r < 1 → ‖term n q‖ ≤ majorant r n) :
    DifferentiableOn ℂ (fun q => ∑' n : ℕ, term n q) (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hSubset : Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball hr₁.le
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := term)
    (majorant_summable hr hr₁) (fun n => (hTerm n).mono hSubset) Metric.isOpen_ball
    (fun n z hz => hBound n (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

theorem printed_differentiableOn_unit_disk :
    DifferentiableOn ℂ printed (Metric.ball (0 : ℂ) 1) := by
  refine analytic_on_unit_disk printedTerm (fun n q hq => ?_) (fun n {q} {r} h hr => printed_bound h hr n)
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  exact ((differentiableAt_id.pow (n ^ 2)).div ((pochhammer_differentiable _).differentiableAt)
    (pochhammer_ne_zero hq₁ _)).differentiableWithinAt

theorem standard_differentiableOn_unit_disk :
    DifferentiableOn ℂ standard (Metric.ball (0 : ℂ) 1) := by
  refine analytic_on_unit_disk standardTerm (fun n q hq => ?_) (fun n {q} {r} h hr => standard_bound h hr n)
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  exact ((differentiableAt_id.pow (n ^ 2)).div (((pochhammer_differentiable _).differentiableAt).pow 2)
    (pow_ne_zero 2 (pochhammer_ne_zero hq₁ _))).differentiableWithinAt

theorem absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖printedTerm n q‖) ∧ Summable (fun n => ‖standardTerm n q‖) :=
  ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => printed_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq),
   Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => standard_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq)⟩

end
end ManuscriptAudit.Paper8InsideComplexAnalytic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8InsideComplexAnalytic.pochhammer_lower,
      ``ManuscriptAudit.Paper8InsideComplexAnalytic.pochhammer_ne_zero,
      ``ManuscriptAudit.Paper8InsideComplexAnalytic.absolute_summability,
      ``ManuscriptAudit.Paper8InsideComplexAnalytic.printed_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8InsideComplexAnalytic.standard_differentiableOn_unit_disk] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
