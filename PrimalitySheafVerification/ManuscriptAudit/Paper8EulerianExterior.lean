import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DoubledExterior

/-!
# The literal Eulerian reciprocal series on physical p. 335

The shifted index `n+1` gives sign `(-1)^n` in the displayed Eulerian
series. Reciprocation changes the exponent to `n(n+1)/2`. The resulting
sum is absolutely convergent and holomorphic in the inverted disk
coordinate, with value two at its center.
-/

namespace ManuscriptAudit.Paper8EulerianExterior

open Paper8InsideComplexAnalytic Paper8ExteriorComplex Paper8DoubledExterior

noncomputable section

def starTerm (n : ℕ) (q : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * q ^ (n + 1) / pochhammer q (n + 1)

def star (q : ℂ) : ℂ := 1 + ∑' n : ℕ, starTerm n q

def reciprocalStarTerm (n : ℕ) (q : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * q ^ (n * (n + 1) / 2) / pochhammer q (n + 1)

def reciprocalStar (q : ℂ) : ℂ := 1 + ∑' n : ℕ, reciprocalStarTerm n q

private theorem two_mul_sum_range (n : ℕ) :
    2 * (∑ j ∈ Finset.range n, (j + 1)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

private theorem triangular_sum_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (j + 1)) = n * (n + 1) / 2 := by
  have h := two_mul_sum_range n
  omega

private theorem triangular_exponent_ge (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => decide
  | succ n =>
      have h := Nat.mul_le_mul_left (n + 1) (show 2 ≤ n + 1 + 1 by omega)
      rw [Nat.mul_comm (n + 1) 2] at h
      omega

theorem star_term_inv_eq {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    starTerm n q⁻¹ = reciprocalStarTerm n q := by
  have hProd := inverse_pochhammer_times_power q hq₀ (n + 1)
  rw [Finset.sum_range_succ, triangular_sum_range n] at hProd
  have hDenom : pochhammer q⁻¹ (n + 1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hProd
    exact pochhammer_ne_zero hq (n + 1) hProd.symm
  have hNum : (q⁻¹) ^ (n + 1) * q ^ (n * (n + 1) / 2 + (n + 1)) =
      q ^ (n * (n + 1) / 2) := by
    have hPow : q ^ (n * (n + 1) / 2 + (n + 1)) =
        q ^ (n + 1) * q ^ (n * (n + 1) / 2) := by
      rw [add_comm (n * (n + 1) / 2), pow_add q (n + 1) (n * (n + 1) / 2)]
    rw [inv_pow, hPow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero (n + 1) hq₀), one_mul]
  unfold starTerm reciprocalStarTerm
  apply (div_eq_div_iff hDenom (pochhammer_ne_zero hq _)).mpr
  rw [← hProd]
  calc
    _ = ((-1 : ℂ) ^ n * ((q⁻¹) ^ (n + 1) * q ^ (n * (n + 1) / 2 + (n + 1)))) *
          pochhammer q⁻¹ (n + 1) := by ring
    _ = _ := by rw [hNum]

theorem star_inv_eq_reciprocalStar {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    star q⁻¹ = reciprocalStar q := by
  unfold star reciprocalStar
  simp_rw [star_term_inv_eq hq₀ hq]

private theorem term_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖reciprocalStarTerm n q‖ ≤ r ^ n / radialFloor r := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  have hPow : ‖q‖ ^ (n * (n + 1) / 2) ≤ r ^ n :=
    (pow_le_pow_left₀ (norm_nonneg q) hqr _).trans
      (pow_le_pow_of_le_one hr h₁.le (triangular_exponent_ge n))
  rw [reciprocalStarTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  calc
    _ ≤ r ^ n / ‖pochhammer q (n + 1)‖ :=
      div_le_div_of_nonneg_right hPow (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hr n) (radialFloor_pos hr h₁)
      (pochhammer_uniform_lower hqr h₁ _)

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ n / radialFloor r) := by
  simpa only [div_eq_mul_inv] using (summable_geometric_of_lt_one hr h₁).mul_right (radialFloor r)⁻¹

theorem reciprocalStar_absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖reciprocalStarTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq)

theorem star_absolute_summability_at_inverse {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n => ‖starTerm n q⁻¹‖) := by
  simp_rw [star_term_inv_eq hq₀ hq]
  exact reciprocalStar_absolute_summability hq

theorem reciprocalStar_differentiableOn_unit_disk :
    DifferentiableOn ℂ reciprocalStar (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (reciprocalStarTerm n) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa only [dist_zero_right] using Metric.mem_ball.mp hz
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (-1 : ℂ) ^ n) z := differentiableAt_const _
    exact ((hc.mul (differentiableAt_id.pow (n * (n + 1) / 2))).div
      ((pochhammer_differentiable (n + 1)).differentiableAt)
      (pochhammer_ne_zero (hz'.trans hr₁) (n + 1))).differentiableWithinAt
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := reciprocalStarTerm)
    (majorant_summable hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      term_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((differentiableAt_const (c := (1 : ℂ))).add
    ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr))).differentiableWithinAt

theorem reciprocalStar_at_zero : reciprocalStar 0 = 2 := by
  unfold reciprocalStar
  rw [tsum_eq_single 0 (fun n hn => by
    have hExp := (Nat.pos_of_ne_zero hn).trans_le (triangular_exponent_ge n)
    simp [reciprocalStarTerm, zero_pow hExp.ne'])]
  norm_num [reciprocalStarTerm, pochhammer, Finset.prod_range_succ]

end
end ManuscriptAudit.Paper8EulerianExterior

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianExterior.star_term_inv_eq,
      ``ManuscriptAudit.Paper8EulerianExterior.star_inv_eq_reciprocalStar,
      ``ManuscriptAudit.Paper8EulerianExterior.reciprocalStar_absolute_summability,
      ``ManuscriptAudit.Paper8EulerianExterior.star_absolute_summability_at_inverse,
      ``ManuscriptAudit.Paper8EulerianExterior.reciprocalStar_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8EulerianExterior.reciprocalStar_at_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
