import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import PrimalitySheafVerification.ManuscriptAudit.Paper8CutoffLog
import PrimalitySheafVerification.ManuscriptAudit.Paper8UnshiftedZeroMode

/-! The positive Abel kernel turning a square-root main term into half a logarithm. -/

namespace ManuscriptAudit.Paper8SqrtAbelKernel

open Filter
open scoped Topology
open Paper8CutoffLog (cutoffLog cutoffLog_pos cutoffLog_tendsto_atTop)
open Paper8UnshiftedZeroMode (squareRootScale)

noncomputable section

def sqrtAbelKernel (n : ℕ) : ℝ := 1 - squareRootScale n / squareRootScale (n + 1)

theorem sqrtAbelKernel_bounds (n : ℕ) :
    1 / (2 * ((n + 2 : ℕ) : ℝ)) ≤ sqrtAbelKernel n ∧
      sqrtAbelKernel n ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  let a := squareRootScale n
  let b := squareRootScale (n + 1)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = ((n + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (n + 1))
  have hEq : (b - a) * (b + a) = 1 := by
    push_cast at ha2 hb2
    nlinarith only [ha2, hb2]
  have hSum : 0 < b + a := add_pos hb ha
  have hRoot : b - a = 1 / (b + a) := (eq_div_iff hSum.ne').2 hEq
  have hRecip : sqrtAbelKernel n = 1 / (b * (b + a)) := by
    change 1 - a / b = _
    calc
      _ = (b - a) / b := by field_simp [hb.ne'] <;> ring
      _ = _ := by rw [hRoot]; field_simp [hb.ne', hSum.ne'] <;> ring
  have hLow : 2 * ((n + 1 : ℕ) : ℝ) ≤ b * (b + a) := by
    calc
      _ = a * (a + a) := by nlinarith only [ha2]
      _ ≤ _ := mul_le_mul hab (add_le_add_left hab a) (add_nonneg ha.le ha.le) hb.le
  have hHigh : b * (b + a) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    calc
      _ ≤ b * (b + b) := mul_le_mul_of_nonneg_left (add_le_add_right hab b) hb.le
      _ = _ := by nlinarith only [hb2]
  rw [hRecip]
  exact ⟨one_div_le_one_div_of_le (mul_pos hb hSum) hHigh,
    one_div_le_one_div_of_le (by positivity) hLow⟩

theorem sqrtAbelKernel_nonneg (n : ℕ) : 0 ≤ sqrtAbelKernel n :=
  (by positivity : 0 ≤ 1 / (2 * ((n + 2 : ℕ) : ℝ))).trans (sqrtAbelKernel_bounds n).1

private theorem ratio_of_sub_log_limit (f : ℕ → ℝ) {c : ℝ}
    (hf : Tendsto (fun N => f N - cutoffLog N) atTop (𝓝 c)) :
    Tendsto (fun N => f N / cutoffLog N) atTop (𝓝 1) := by
  have hi : Tendsto (fun N => (cutoffLog N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp cutoffLog_tendsto_atTop
  have hSmall : Tendsto (fun N => (f N - cutoffLog N) / cutoffLog N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hf.mul hi
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun N => 1 + (f N - cutoffLog N) / cutoffLog N) atTop (𝓝 1) := by
    simpa only [add_zero] using hOne.add hSmall
  apply h.congr
  intro N
  field_simp [(cutoffLog_pos N).ne'] <;> ring

private theorem harmonic_shifted_sub_log :
    Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ) - cutoffLog N) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have hN : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun n hn => ?_
    exact hn.trans (Nat.le_succ n)
  refine (Real.tendsto_harmonic_sub_log_add_one.comp hN).congr fun N => ?_
  have hArg : ((N + 1 : ℕ) : ℝ) + 1 = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
  change (harmonic (N + 1) : ℝ) - Real.log (((N + 1 : ℕ) : ℝ) + 1) = _
  rw [hArg, cutoffLog]

private theorem harmonic_ratio :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / cutoffLog N) atTop (𝓝 1) := by
  apply ratio_of_sub_log_limit
  have hN : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun n hn => ?_
    exact hn.trans (Nat.le_succ n)
  have hInv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hN)
  refine (harmonic_shifted_sub_log.sub hInv).congr fun N => ?_
  rw [harmonic_succ]
  push_cast
  ring

private theorem harmonic_tail_ratio :
    Tendsto (fun N : ℕ => ((harmonic (N + 1) : ℝ) - 1) / cutoffLog N) atTop (𝓝 1) := by
  apply ratio_of_sub_log_limit
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact (harmonic_shifted_sub_log.sub hOne).congr (fun N => by ring)

private theorem harmonic_cast_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem sqrtAbelKernel_log_mean :
    Tendsto (fun N => (∑ n ∈ Finset.range N, sqrtAbelKernel n) / cutoffLog N) atTop (𝓝 (1 / 2)) := by
  have hHalf : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hLo : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * (((harmonic (N + 1) : ℝ) - 1) / cutoffLog N)) atTop (𝓝 (1 / 2)) := by
    simpa only [mul_one] using hHalf.mul harmonic_tail_ratio
  have hHi : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * ((harmonic N : ℝ) / cutoffLog N)) atTop (𝓝 (1 / 2)) := by
    simpa only [mul_one] using hHalf.mul harmonic_ratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLo hHi ?_ ?_
  · intro N
    change (1 / 2 : ℝ) * (((harmonic (N + 1) : ℝ) - 1) / cutoffLog N) ≤
      (∑ n ∈ Finset.range N, sqrtAbelKernel n) / cutoffLog N
    have hTail : (harmonic (N + 1) : ℝ) - 1 =
        ∑ n ∈ Finset.range N, ((n + 2 : ℕ) : ℝ)⁻¹ := by
      rw [harmonic_cast_sum, Finset.sum_range_succ']
      simp only [zero_add, Nat.cast_one, inv_one, add_sub_cancel_right]
    rw [hTail, ← mul_div_assoc, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (cutoffLog_pos N).le
    refine Finset.sum_le_sum fun n _ => ?_
    calc
      _ = 1 / (2 * ((n + 2 : ℕ) : ℝ)) := by
        have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hn] <;> ring
      _ ≤ _ := (sqrtAbelKernel_bounds n).1
  · intro N
    change (∑ n ∈ Finset.range N, sqrtAbelKernel n) / cutoffLog N ≤
      (1 / 2 : ℝ) * ((harmonic N : ℝ) / cutoffLog N)
    rw [harmonic_cast_sum, ← mul_div_assoc, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (cutoffLog_pos N).le
    refine Finset.sum_le_sum fun n _ => ?_
    calc
      _ ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) := (sqrtAbelKernel_bounds n).2
      _ = _ := by
        have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hn] <;> ring

end
end ManuscriptAudit.Paper8SqrtAbelKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SqrtAbelKernel.sqrtAbelKernel_bounds,
      ``ManuscriptAudit.Paper8SqrtAbelKernel.sqrtAbelKernel_log_mean] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
