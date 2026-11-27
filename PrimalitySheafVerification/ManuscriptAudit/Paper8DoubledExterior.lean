import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplexHolomorphy

/-!
# The reciprocal series for the doubled index printed on physical p. 341

The index on the product in the worked example is `2n`. Its n-th term
at the reciprocal argument has numerator `q^(n(n+1))`, with the same
doubled-index product evaluated at `q`.
-/

namespace ManuscriptAudit.Paper8DoubledExterior

open Paper8InsideComplexAnalytic Paper8ExteriorComplex

noncomputable section

def doubledExteriorTerm (n : ℕ) (q : ℂ) : ℂ :=
  q ^ (n * (n + 1)) / pochhammer q (2 * n)

def doubledExterior (q : ℂ) : ℂ := ∑' n : ℕ, doubledExteriorTerm n q

private theorem pochhammer_succ (q : ℂ) (n : ℕ) :
    pochhammer q (n + 1) = pochhammer q n * (1 + q ^ (n + 1)) := by
  simp only [pochhammer, Finset.prod_range_succ]

private theorem inverse_pochhammer_times_power (q : ℂ) (hq : q ≠ 0) (n : ℕ) :
    pochhammer q⁻¹ n * q ^ (∑ j ∈ Finset.range n, (j + 1)) = pochhammer q n := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
      have hFactor : (1 + q⁻¹ ^ (n + 1)) * q ^ (n + 1) = 1 + q ^ (n + 1) := by
        rw [add_mul, one_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
        exact add_comm _ _
      rw [pochhammer_succ, pochhammer_succ, Finset.sum_range_succ, pow_add]
      calc
        _ = (pochhammer q⁻¹ n * q ^ (∑ j ∈ Finset.range n, (j + 1))) *
            ((1 + q⁻¹ ^ (n + 1)) * q ^ (n + 1)) := by ring
        _ = _ := by rw [ih, hFactor]

private theorem sum_range_doubled (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n), (j + 1)) = n * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

theorem printed_term_inv_eq {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    printedTerm n q⁻¹ = doubledExteriorTerm n q := by
  have hProd := inverse_pochhammer_times_power q hq₀ (2 * n)
  rw [sum_range_doubled] at hProd
  have hDenom : pochhammer q⁻¹ (2 * n) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hProd
    exact pochhammer_ne_zero hq (2 * n) hProd.symm
  have hNum : (q⁻¹) ^ (n ^ 2) * q ^ (n * (2 * n + 1)) = q ^ (n * (n + 1)) := by
    rw [show n * (2 * n + 1) = n ^ 2 + n * (n + 1) by ring, inv_pow, pow_add,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq₀), one_mul]
  unfold printedTerm doubledExteriorTerm
  apply (div_eq_div_iff hDenom (pochhammer_ne_zero hq _)).mpr
  rw [← hProd]
  calc
    _ = ((q⁻¹) ^ (n ^ 2) * q ^ (n * (2 * n + 1))) * pochhammer q⁻¹ (2 * n) := by ring
    _ = _ := by rw [hNum]

theorem printed_inv_eq_doubledExterior {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    printed q⁻¹ = doubledExterior q := by
  unfold printed doubledExterior
  simp_rw [printed_term_inv_eq hq₀ hq]

private theorem term_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖doubledExteriorTerm n q‖ ≤ r ^ n / radialFloor r := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  have hPow : r ^ (n * (n + 1)) ≤ r ^ n := by
    rw [show n * (n + 1) = n + n ^ 2 by ring, pow_add]
    have hPow' : r ^ (n ^ 2) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr h₁.le (n ^ 2)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hPow' (pow_nonneg hr n)
  rw [doubledExteriorTerm, norm_div, norm_pow]
  calc
    _ ≤ r ^ n / ‖pochhammer q (2 * n)‖ := div_le_div_of_nonneg_right
      ((pow_le_pow_left₀ (norm_nonneg q) hqr _).trans hPow) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hr n) (radialFloor_pos hr h₁)
      (pochhammer_uniform_lower hqr h₁ _)

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ n / radialFloor r) := by
  simpa only [div_eq_mul_inv] using (summable_geometric_of_lt_one hr h₁).mul_right (radialFloor r)⁻¹

theorem doubledExterior_absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖doubledExteriorTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq)

theorem printed_absolute_summability_at_inverse {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n => ‖printedTerm n q⁻¹‖) := by
  simp_rw [printed_term_inv_eq hq₀ hq]
  exact doubledExterior_absolute_summability hq

private theorem pochhammer_differentiable (n : ℕ) :
    Differentiable ℂ (fun q => pochhammer q n) := by
  induction n with
  | zero => simpa [pochhammer] using differentiable_const (c := (1 : ℂ))
  | succ n ih =>
      simp_rw [pochhammer_succ]
      exact ih.mul (by fun_prop)

theorem doubledExterior_differentiableOn_unit_disk :
    DifferentiableOn ℂ doubledExterior (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (doubledExteriorTerm n) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa only [dist_zero_right] using Metric.mem_ball.mp hz
    exact ((differentiableAt_id.pow (n * (n + 1))).div
      ((pochhammer_differentiable (2 * n)).differentiableAt)
      (pochhammer_ne_zero (hz'.trans hr₁) (2 * n))).differentiableWithinAt
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := doubledExteriorTerm)
    (majorant_summable hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      term_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

/-- The fractional weight in the worked example on a chosen local root. -/
theorem normalized_doubled_branch_differentiableOn {s : Set ℂ} {root : ℂ → ℂ}
    (hRoot : DifferentiableOn ℂ root s)
    (hDomain : ∀ q ∈ s, q ≠ 0 ∧ ‖q‖ < 1) :
    DifferentiableOn ℂ (fun q => root q * printed q⁻¹) s := by
  have hSub : s ⊆ Metric.ball (0 : ℂ) 1 := fun q hq => by
    simpa [Metric.mem_ball, dist_zero_right] using (hDomain q hq).2
  refine (hRoot.mul (doubledExterior_differentiableOn_unit_disk.mono hSub)).congr ?_
  intro q hq
  change root q * printed q⁻¹ = root q * doubledExterior q
  rw [printed_inv_eq_doubledExterior (hDomain q hq).1 (hDomain q hq).2]

end
end ManuscriptAudit.Paper8DoubledExterior

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DoubledExterior.printed_term_inv_eq,
      ``ManuscriptAudit.Paper8DoubledExterior.printed_inv_eq_doubledExterior,
      ``ManuscriptAudit.Paper8DoubledExterior.doubledExterior_absolute_summability,
      ``ManuscriptAudit.Paper8DoubledExterior.printed_absolute_summability_at_inverse,
      ``ManuscriptAudit.Paper8DoubledExterior.doubledExterior_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8DoubledExterior.normalized_doubled_branch_differentiableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
