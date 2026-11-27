import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplex

/-!
# Complex holomorphy of the literal exterior series

The exterior series has an unweighted holomorphic expression in the inverted
disk coordinate. The fractional weight on physical pp. 324, 332 and 383 is
holomorphic on the root coordinate `q=w^24`, or on any chosen holomorphic
branch of this root.
-/

namespace ManuscriptAudit.Paper8ExteriorComplexHolomorphy

open Set Paper8InsideComplexAnalytic Paper8ExteriorComplex

noncomputable section

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

private theorem exteriorTerm_differentiableAt (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (exteriorTerm n) q :=
  (differentiableAt_id.pow n).div (((pochhammer_differentiable n).differentiableAt).pow 2)
    (pow_ne_zero 2 (pochhammer_ne_zero hq n))

theorem exterior_differentiableOn_unit_disk :
    DifferentiableOn ℂ exterior (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hDiff (n : ℕ) : DifferentiableOn ℂ (exteriorTerm n) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa only [dist_zero_right] using Metric.mem_ball.mp hz
    exact (exteriorTerm_differentiableAt n (hz'.trans hr₁)).differentiableWithinAt
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := exteriorTerm)
    (radialMajorant_summable hr hr₁) hDiff Metric.isOpen_ball
    (fun n z hz => exteriorTerm_bound
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

private theorem ne_zero_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) : z ≠ 0 := by
  exact norm_pos_iff.mp (zero_lt_one.trans hz)

private theorem norm_inv_lt_one {z : ℂ} (hz : 1 < ‖z‖) : ‖z⁻¹‖ < 1 := by
  rw [norm_inv, inv_eq_one_div]
  exact (div_lt_one (zero_lt_one.trans hz)).mpr hz

theorem exterior_absolute_summability_outside {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun n => ‖standardTerm n z‖) := by
  simpa only [inv_inv] using absolute_summability_at_inverse
    (inv_ne_zero (ne_zero_of_one_lt_norm hz)) (norm_inv_lt_one hz)

theorem standard_differentiableOn_exterior :
    DifferentiableOn ℂ standard {z : ℂ | 1 < ‖z‖} := by
  have hInv : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | 1 < ‖z‖} :=
    fun z hz => ((differentiableAt_inv_iff).mpr (ne_zero_of_one_lt_norm hz)).differentiableWithinAt
  have hMaps : MapsTo (fun z : ℂ => z⁻¹) {z : ℂ | 1 < ‖z‖} (Metric.ball (0 : ℂ) 1) :=
    fun z hz => by simpa [Metric.mem_ball, dist_zero_right] using norm_inv_lt_one hz
  refine (exterior_differentiableOn_unit_disk.comp hInv hMaps).congr ?_
  intro z hz
  simpa only [Function.comp_apply, inv_inv] using
    standard_inv_eq_exterior (inv_ne_zero (ne_zero_of_one_lt_norm hz)) (norm_inv_lt_one hz)

/-- In the coordinate `q=w^24`, the displayed factor `q^(1/24)` is `w`. -/
def normalizedCover (w : ℂ) : ℂ := w * exterior (w ^ (24 : ℕ))

private theorem norm_pow_twentyFour_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    ‖w ^ (24 : ℕ)‖ < 1 := by
  rw [norm_pow]
  exact (radius_power_le (norm_nonneg w) hw.le 23).trans_lt hw

theorem normalizedCover_eq_literal {w : ℂ} (hw₀ : w ≠ 0) (hw : ‖w‖ < 1) :
    normalizedCover w = w * standard ((w ^ (24 : ℕ))⁻¹) := by
  rw [normalizedCover, standard_inv_eq_exterior (pow_ne_zero _ hw₀) (norm_pow_twentyFour_lt_one hw)]

theorem normalizedCover_literal_absolute_summability {w : ℂ} (hw₀ : w ≠ 0) (hw : ‖w‖ < 1) :
    Summable (fun n => ‖w * standardTerm n ((w ^ (24 : ℕ))⁻¹)‖) := by
  simpa only [norm_mul] using (absolute_summability_at_inverse
    (pow_ne_zero 24 hw₀) (norm_pow_twentyFour_lt_one hw)).mul_left ‖w‖

theorem normalizedCover_differentiableOn_unit_disk :
    DifferentiableOn ℂ normalizedCover (Metric.ball (0 : ℂ) 1) := by
  have hPow : DifferentiableOn ℂ (fun w : ℂ => w ^ (24 : ℕ)) (Metric.ball (0 : ℂ) 1) :=
    (differentiable_id.pow 24).differentiableOn
  have hMaps : MapsTo (fun w : ℂ => w ^ (24 : ℕ)) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
    simpa [Metric.mem_ball, dist_zero_right] using norm_pow_twentyFour_lt_one hw'
  exact differentiableOn_id.mul (exterior_differentiableOn_unit_disk.comp hPow hMaps)

theorem normalizedCover_zero : normalizedCover 0 = 0 := by simp [normalizedCover]

/-- The literal normalized value is holomorphic on any chosen branch domain. -/
theorem normalized_branch_differentiableOn {s : Set ℂ} {root : ℂ → ℂ}
    (hRoot : DifferentiableOn ℂ root s)
    (hDomain : ∀ q ∈ s, q ≠ 0 ∧ ‖q‖ < 1) :
    DifferentiableOn ℂ (fun q => root q * standard q⁻¹) s := by
  have hSub : s ⊆ Metric.ball (0 : ℂ) 1 := fun q hq => by
    simpa [Metric.mem_ball, dist_zero_right] using (hDomain q hq).2
  refine (hRoot.mul (exterior_differentiableOn_unit_disk.mono hSub)).congr ?_
  intro q hq
  rw [standard_inv_eq_exterior (hDomain q hq).1 (hDomain q hq).2]

end
end ManuscriptAudit.Paper8ExteriorComplexHolomorphy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.exterior_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.exterior_absolute_summability_outside,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.standard_differentiableOn_exterior,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.normalizedCover_eq_literal,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.normalizedCover_literal_absolute_summability,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.normalizedCover_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.normalizedCover_zero,
      ``ManuscriptAudit.Paper8ExteriorComplexHolomorphy.normalized_branch_differentiableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
