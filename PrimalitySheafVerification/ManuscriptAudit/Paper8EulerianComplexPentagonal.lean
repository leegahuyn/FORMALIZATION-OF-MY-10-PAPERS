import Lean.Util.CollectAxioms
import Mathlib.Analysis.Analytic.IsolatedZeros
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianPentagonal
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrenceBridge

/-! The Eulerian-pentagonal relation holds on the full complex disk. -/

namespace ManuscriptAudit.Paper8EulerianComplexPentagonal

open Set Paper8EulerianRecurrence Paper8EulerianPentagonal Paper8EulerianRecurrenceBridge
open Paper8EulerianExterior

noncomputable section

def complexTerm (n : ℕ) (q : ℂ) : ℂ := q ^ exponent n * (1 - q ^ (2 * n + 1))

def complexSeries (q : ℂ) : ℂ := ∑' n : ℕ, complexTerm n q

private theorem term_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖complexTerm n q‖ ≤ 2 * r ^ n := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  have hExp : ‖q‖ ^ exponent n ≤ r ^ n :=
    (pow_le_pow_left₀ (norm_nonneg q) hqr _).trans
      (pow_le_pow_of_le_one hr h₁.le (self_le_exponent n))
  have hPower : ‖q‖ ^ (2 * n + 1) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg q) (hqr.trans h₁.le) (2 * n + 1)
  have hSecond : ‖1 - q ^ (2 * n + 1)‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖q ^ (2 * n + 1)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one, norm_pow]; linarith only [hPower]
  rw [complexTerm, norm_mul, norm_pow]
  calc
    _ ≤ r ^ n * 2 := mul_le_mul hExp hSecond (norm_nonneg _) (pow_nonneg hr n)
    _ = _ := mul_comm _ _

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => (2 : ℝ) * r ^ n) :=
  (summable_geometric_of_lt_one hr h₁).mul_left 2

theorem complex_absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖complexTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq)

theorem complexSeries_differentiableOn :
    DifferentiableOn ℂ complexSeries (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (complexTerm n) (Metric.ball (0 : ℂ) r) :=
    ((differentiable_id.pow (exponent n)).mul
      ((differentiable_const (c := (1 : ℂ))).sub (differentiable_id.pow (2 * n + 1)))).differentiableOn
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := complexTerm)
    (majorant_summable hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      term_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

private theorem term_ofReal (q : ℝ) (n : ℕ) : ((pentagonalTerm q n : ℝ) : ℂ) =
    complexTerm n (q : ℂ) := by
  simp only [pentagonalTerm, complexTerm, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow]

theorem complexSeries_ofReal {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    complexSeries (q : ℂ) = (pentagonalSeries q : ℂ) := by
  have h := Complex.ofRealCLM.hasSum (pentagonalTerm_summable hq h₁).hasSum
  change HasSum (fun n => ((pentagonalTerm q n : ℝ) : ℂ)) (pentagonalSeries q : ℂ) at h
  simp only [term_ofReal] at h
  exact h.tsum_eq

theorem reciprocalStar_eq_two_complexSeries {q : ℂ} (hq : ‖q‖ < 1) :
    reciprocalStar q = 2 * complexSeries q := by
  let disk := Metric.ball (0 : ℂ) 1
  have hF : AnalyticOnNhd ℂ reciprocalStar disk :=
    reciprocalStar_differentiableOn_unit_disk.analyticOnNhd Metric.isOpen_ball
  have hConst : DifferentiableOn ℂ (fun _ : ℂ => (2 : ℂ)) disk := differentiableOn_const
  have hG : AnalyticOnNhd ℂ (fun z => (2 : ℂ) * complexSeries z) disk :=
    (hConst.mul complexSeries_differentiableOn).analyticOnNhd Metric.isOpen_ball
  have hC : IsPreconnected disk := (convex_ball (0 : ℂ) 1).isPreconnected
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have hAccum : (0 : ℂ) ∈ closure ({z | reciprocalStar z = (2 : ℂ) * complexSeries z} \ {0}) := by
    refine Metric.mem_closure_iff.mpr ?_
    intro ε hε
    let r : ℝ := min (ε / 2) (1 / 2)
    have hr : 0 < r := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have hεr : r < ε := (min_le_left _ _).trans_lt (by linarith only [hε])
    have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨(r : ℂ), ⟨?_, ?_⟩, ?_⟩
    · change reciprocalStar (r : ℂ) = 2 * complexSeries (r : ℂ)
      rw [reciprocalStar_ofReal_eq_two_H hr.le hr₁, complexSeries_ofReal hr.le hr₁,
        H_one_eq_pentagonalSeries hr.le hr₁]
    · have hz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      simpa using hz
    · simpa only [dist_zero_left, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg hr.le] using hεr
  have hmem : q ∈ disk := by simpa only [disk, Metric.mem_ball, dist_zero_right] using hq
  exact hF.eqOn_of_preconnected_of_mem_closure hG hC h0 hAccum hmem

end
end ManuscriptAudit.Paper8EulerianComplexPentagonal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianComplexPentagonal.complex_absolute_summability,
      ``ManuscriptAudit.Paper8EulerianComplexPentagonal.complexSeries_differentiableOn,
      ``ManuscriptAudit.Paper8EulerianComplexPentagonal.complexSeries_ofReal,
      ``ManuscriptAudit.Paper8EulerianComplexPentagonal.reciprocalStar_eq_two_complexSeries] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
