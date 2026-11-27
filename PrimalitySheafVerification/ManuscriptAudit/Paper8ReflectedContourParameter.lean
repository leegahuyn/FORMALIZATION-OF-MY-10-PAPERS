import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourParameter

/-! Reflection of the regular contour factor transfers the fixed-disk estimates to the inverse nome. -/

namespace ManuscriptAudit.Paper8ReflectedContourParameter

open Metric Set
open Paper8FixedContourParameter
  (fixedRadius regular factor denominator regular_differentiableOn regular_norm_le_four
    regular_difference_norm_le)

noncomputable section

theorem regular_reflect (α β : ℝ) (ζ q s : ℂ) :
    regular (-α) (-β) ζ q s = regular α β ζ q (-s) := by
  simp only [regular, denominator, factor, Complex.ofReal_neg, neg_mul, mul_neg]

theorem reflected_differentiableOn (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    DifferentiableOn ℂ (regular (-α) (-β) ζ q) (closedBall (0 : ℂ) fixedRadius) := by
  have hFun : regular (-α) (-β) ζ q = (regular α β ζ q) ∘ (fun s : ℂ => -s) :=
    funext (regular_reflect α β ζ q)
  rw [hFun]
  have hNeg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
  exact (regular_differentiableOn α hβ hβ' hζ hq).comp hNeg.differentiableOn (by
    intro s hs
    simpa only [mem_closedBall, dist_zero_right, norm_neg] using hs)

theorem reflected_norm_le_four {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24) (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q s : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    ‖regular (-α) (-β) ζ q s‖ ≤ 4 := by
  rw [regular_reflect]
  exact regular_norm_le_four hα hα' hβ hβ' hζ hq (by simpa only [norm_neg] using hs)

theorem reflected_difference_norm_le {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24) (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {ζ q s : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    ‖regular (-α) (-β) ζ q s - regular (-α) (-β) ζ 0 s‖ ≤ 8 * ‖q‖ := by
  rw [regular_reflect α β ζ q, regular_reflect α β ζ 0]
  exact regular_difference_norm_le hα hα' hβ hβ' hζ hq (by simpa only [norm_neg] using hs)

end
end ManuscriptAudit.Paper8ReflectedContourParameter

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReflectedContourParameter.regular_reflect,
      ``ManuscriptAudit.Paper8ReflectedContourParameter.reflected_differentiableOn,
      ``ManuscriptAudit.Paper8ReflectedContourParameter.reflected_norm_le_four,
      ``ManuscriptAudit.Paper8ReflectedContourParameter.reflected_difference_norm_le] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
