import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper8LocalContour

/-! Independence of the small positive radius in either local contour kernel. -/

namespace ManuscriptAudit.Paper8ContourRadius

open Metric Set
open Paper8LocalContour (root denominator factor integrand denominator_ne_zero_of_small_norm)
open Paper8ContourGammaSeries (a differentiableOn_punctured)
open Paper8HolomorphicPartPhase (qParameter)

noncomputable section

private theorem integrand_differentiableAt {k : ℕ} (hk : 0 < k) (d : ℤ) (α β : ℝ)
    {z s : ℂ} (hs : s ≠ 0) (hDen : denominator β k d z s ≠ 0) :
    DifferentiableAt ℂ (integrand α β k d z) s := by
  have hOpen : IsOpen {w : ℂ | w ≠ 0} := isClosed_singleton.isOpen_compl
  have ha := ((differentiableOn_punctured hk) s hs).differentiableAt (hOpen.mem_nhds hs)
  have hExp (t : ℝ) : Differentiable ℂ (fun w : ℂ => Complex.exp ((t : ℂ) * w)) :=
    Complex.differentiable_exp.comp ((differentiable_const (c := (t : ℂ))).mul differentiable_id)
  have hOne : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) :=
    differentiable_const (c := (1 : ℂ))
  have hD : Differentiable ℂ (denominator β k d z) :=
    hOne.sub ((differentiable_const (c := root k ^ d * qParameter z)).mul (hExp β))
  exact (ha.mul (hExp α s)).div (hD s) hDen

theorem circleIntegral_eq_of_small_radii {k : ℕ} (hk : 0 < k) (d : ℤ) (α : ℝ)
    {β : ℝ} (hβ : 0 < β) {z : ℂ} {r R : ℝ} (hr : 0 < r) (hle : r ≤ R)
    (hSafe : β * R < 2 * Real.pi * |z.im|) :
    circleIntegral (integrand α β k d z) 0 R = circleIntegral (integrand α β k d z) 0 r := by
  have hd (s : ℂ) (hs₀ : 0 < ‖s‖) (hsR : ‖s‖ ≤ R) :
      DifferentiableAt ℂ (integrand α β k d z) s :=
    integrand_differentiableAt hk d α β (norm_pos_iff.mp hs₀)
      (denominator_ne_zero_of_small_norm hβ k d ((mul_le_mul_of_nonneg_left hsR hβ.le).trans_lt hSafe))
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle
    (s := ∅) Set.countable_empty ?_ ?_
  · intro s hs
    have hLo : r ≤ ‖s‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hs.2
    have hHi : ‖s‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs.1
    exact (hd s (hr.trans_le hLo) hHi).continuousAt.continuousWithinAt
  · intro s hs
    have hLo : r < ‖s‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hs.1.2
    have hHi : ‖s‖ < R := by simpa only [mem_ball, dist_zero_right] using hs.1.1
    exact hd s (hr.trans hLo) hHi.le

end
end ManuscriptAudit.Paper8ContourRadius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ContourRadius.circleIntegral_eq_of_small_radii
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
