import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerRealAxis

/-! The discontinuity of the common-argument elliptic product persists on its pole-free real slice. -/

namespace ManuscriptAudit.Paper7CommonEulerRealLimit

open Filter Topology Paper7ActualCommonEuler Paper7CommonEulerRealAxis
open Paper7CommonEulerLocalDecay Paper7CommonEulerPointwise

theorem finite_product_continuous_at_zero (n : ℕ) :
    ContinuousAt (fun z : ℂ => partialProduct goodPrime trace z n) 0 := by
  induction n with
  | zero =>
    simpa only [partialProduct, Finset.range_zero, Finset.prod_empty] using
      (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) 0)
  | succ n ih =>
    have he : (fun z : ℂ => partialProduct goodPrime trace z (n+1)) =
        fun z : ℂ => partialProduct goodPrime trace z n *
          (denominator (goodPrime n) (trace n) z)⁻¹ := by
      funext z
      simp only [partialProduct, Finset.prod_range_succ]
    rw [he]
    have hc : Continuous (denominator (goodPrime n) (trace n)) := by
      unfold denominator
      fun_prop
    exact ih.mul (hc.continuousAt.inv₀ (by simp [denominator]))

theorem no_continuous_pointwise_limit_on_real_slice {r : ℝ} (hr : 0 < r) :
    ¬ ∃ g : ℝ → ℂ, ContinuousAt g 0 ∧ ∀ x : ℝ, 0 ≤ x → x < r →
      Tendsto (partialProduct goodPrime trace (x : ℂ)) atTop (𝓝 (g x)) := by
  rintro ⟨g, hg, h⟩
  apply actual_no_continuous_common_argument hr
  refine ⟨fun z : ℂ => g ‖z‖, ?_, fun z hz => ?_⟩
  · have hC : ContinuousAt g ‖(0 : ℂ)‖ := by simpa only [norm_zero] using hg
    exact hC.comp continuous_norm.continuousAt
  · rcases eq_or_ne z 0 with rfl | hne
    · simpa only [norm_zero, Complex.ofReal_zero] using h 0 le_rfl hr
    · have hx : ‖z‖ ≠ 0 := (norm_pos_iff.mpr hne).ne'
      have hZero := actual_product_tendsto_zero_on_real_axis hx
      have hg0 := tendsto_nhds_unique (h ‖z‖ (norm_nonneg _) hz) hZero
      rw [hg0]
      exact tendsto_at_nonzero goodPrime_tendsto trace_hasse hne

end ManuscriptAudit.Paper7CommonEulerRealLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerRealLimit.finite_product_continuous_at_zero,
      ``ManuscriptAudit.Paper7CommonEulerRealLimit.no_continuous_pointwise_limit_on_real_slice] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
