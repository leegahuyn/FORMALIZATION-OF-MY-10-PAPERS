import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper8LocalContour

/-! Regular factors of both contour integrands on one fixed q-disk and s-circle. -/

namespace ManuscriptAudit.Paper8FixedContourParameter

open Metric Set

noncomputable section

def fixedRadius : ℝ := Real.log 2 / 24

theorem fixedRadius_pos : 0 < fixedRadius := by
  unfold fixedRadius
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

def factor (β : ℝ) (ζ q s : ℂ) : ℂ := ζ * q * Complex.exp ((β : ℂ) * s)

def denominator (β : ℝ) (ζ q s : ℂ) : ℂ := 1 - factor β ζ q s

def regular (α β : ℝ) (ζ q s : ℂ) : ℂ :=
  Complex.exp ((α : ℂ) * s) / denominator β ζ q s

private theorem exp_norm_le_two {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 24) {s : ℂ}
    (hs : ‖s‖ ≤ fixedRadius) : ‖Complex.exp ((t : ℂ) * s)‖ ≤ 2 := by
  have hRe : s.re ≤ fixedRadius := (le_abs_self _).trans ((Complex.abs_re_le_norm s).trans hs)
  have hExp : Real.exp (24 * fixedRadius) = 2 := by
    have hArg : 24 * fixedRadius = Real.log 2 := by unfold fixedRadius; ring
    rw [hArg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ Real.exp (t * fixedRadius) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hRe ht)
    _ ≤ Real.exp (24 * fixedRadius) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht' fixedRadius_pos.le)
    _ = _ := hExp

private theorem factor_norm_bound {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q s : ℂ} (hζ : ‖ζ‖ = 1) (hs : ‖s‖ ≤ fixedRadius) :
    ‖factor β ζ q s‖ ≤ 2 * ‖q‖ := by
  simp only [factor, norm_mul, hζ, one_mul]
  rw [mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (exp_norm_le_two hβ hβ' hs) (norm_nonneg _)

theorem denominator_norm_lower {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q s : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    (1 / 2 : ℝ) ≤ ‖denominator β ζ q s‖ := by
  have hF := factor_norm_bound (q := q) hβ hβ' hζ hs
  have hSub := norm_sub_norm_le (1 : ℂ) (factor β ζ q s)
  simp only [norm_one] at hSub
  change (1 / 2 : ℝ) ≤ ‖1 - factor β ζ q s‖
  linarith

theorem denominator_ne_zero {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q s : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    denominator β ζ q s ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (denominator_norm_lower hβ hβ' hζ hq hs))

theorem regular_at_zero (α β : ℝ) (ζ s : ℂ) :
    regular α β ζ 0 s = Complex.exp ((α : ℂ) * s) := by
  simp [regular, denominator, factor]

theorem regular_s_zero (α β : ℝ) (ζ q : ℂ) : regular α β ζ q 0 = 1 / (1 - ζ * q) := by
  simp [regular, denominator, factor]

theorem regular_norm_le_four {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {ζ q s : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    ‖regular α β ζ q s‖ ≤ 4 := by
  rw [regular, norm_div]
  calc
    _ ≤ 2 / ‖denominator β ζ q s‖ :=
      div_le_div_of_nonneg_right (exp_norm_le_two hα hα' hs) (norm_nonneg _)
    _ ≤ (2 : ℝ) / (1 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (denominator_norm_lower hβ hβ' hζ hq hs)
    _ = _ := by norm_num

theorem regular_difference_norm_le {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {ζ q s : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    ‖regular α β ζ q s - regular α β ζ 0 s‖ ≤ 8 * ‖q‖ := by
  have hd : 1 - factor β ζ q s ≠ 0 := denominator_ne_zero hβ hβ' hζ hq hs
  have hEq : regular α β ζ q s - regular α β ζ 0 s =
      (Complex.exp ((α : ℂ) * s) * factor β ζ q s) / denominator β ζ q s := by
    rw [regular_at_zero]
    unfold regular denominator
    field_simp [hd] <;> ring
  rw [hEq, norm_div, norm_mul]
  calc
    _ ≤ (2 * (2 * ‖q‖)) / ‖denominator β ζ q s‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (exp_norm_le_two hα hα' hs) (factor_norm_bound hβ hβ' hζ hs)
        (norm_nonneg _) (by norm_num)
    _ ≤ (2 * (2 * ‖q‖)) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (denominator_norm_lower hβ hβ' hζ hq hs)
    _ = _ := by ring

theorem regular_differentiableOn (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    DifferentiableOn ℂ (regular α β ζ q) (closedBall (0 : ℂ) fixedRadius) := by
  have hExp (t : ℝ) : Differentiable ℂ (fun s : ℂ => Complex.exp ((t : ℂ) * s)) :=
    Complex.differentiable_exp.comp ((differentiable_const (c := (t : ℂ))).mul differentiable_id)
  have hOne : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := differentiable_const (c := (1 : ℂ))
  have hDen : Differentiable ℂ (denominator β ζ q) :=
    hOne.sub ((differentiable_const (c := ζ * q)).mul (hExp β))
  exact (hExp α).differentiableOn.div hDen.differentiableOn (fun s hs =>
    denominator_ne_zero hβ hβ' hζ hq (by simpa only [mem_closedBall, dist_zero_right] using hs))

end
end ManuscriptAudit.Paper8FixedContourParameter

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FixedContourParameter.fixedRadius_pos,
      ``ManuscriptAudit.Paper8FixedContourParameter.denominator_norm_lower,
      ``ManuscriptAudit.Paper8FixedContourParameter.denominator_ne_zero,
      ``ManuscriptAudit.Paper8FixedContourParameter.regular_at_zero,
      ``ManuscriptAudit.Paper8FixedContourParameter.regular_s_zero,
      ``ManuscriptAudit.Paper8FixedContourParameter.regular_norm_le_four,
      ``ManuscriptAudit.Paper8FixedContourParameter.regular_difference_norm_le,
      ``ManuscriptAudit.Paper8FixedContourParameter.regular_differentiableOn] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
