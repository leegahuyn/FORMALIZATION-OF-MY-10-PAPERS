import Lean.Util.CollectAxioms
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.BigOperators.Module
import PrimalitySheafVerification.ManuscriptAudit.Paper8SqrtAbelKernel

/-! Abel summation transfers a square-root partial main term to half a logarithm. -/

namespace ManuscriptAudit.Paper8SqrtAbelLogTransfer

open Filter Asymptotics
open scoped Topology
open Paper8CutoffLog (cutoffLog cutoffLog_pos cutoffLog_tendsto_atTop)
open Paper8UnshiftedZeroMode (squareRootScale)
open Paper8SqrtAbelKernel (sqrtAbelKernel sqrtAbelKernel_nonneg sqrtAbelKernel_log_mean)

noncomputable section

theorem sqrtAbel_weighted_mean (u : ℕ → ℂ) {A : ℂ} (hU : Tendsto u atTop (𝓝 A)) :
    Tendsto (fun N => (cutoffLog N)⁻¹ • ∑ j ∈ Finset.range N, sqrtAbelKernel j • u j)
      atTop (𝓝 ((1 / 2 : ℝ) • A)) := by
  let S (N : ℕ) := ∑ j ∈ Finset.range N, sqrtAbelKernel j
  let E (j : ℕ) := sqrtAbelKernel j • (u j - A)
  have hSmall : Tendsto (fun j => u j - A) atTop (𝓝 0) := by
    have hA : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    simpa only [sub_self] using hU.sub hA
  have hE : E =o[atTop] sqrtAbelKernel := by
    refine isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hSmall ε hε] with j hj
    rw [dist_zero_right] at hj
    change ‖sqrtAbelKernel j • (u j - A)‖ ≤ ε * ‖sqrtAbelKernel j‖
    rw [norm_smul, Real.norm_of_nonneg (sqrtAbelKernel_nonneg j), mul_comm ε]
    exact mul_le_mul_of_nonneg_left hj.le (sqrtAbelKernel_nonneg j)
  have hS : Tendsto S atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_order.1 sqrtAbelKernel_log_mean).1 (1 / 4) (by norm_num),
      tendsto_atTop.1 cutoffLog_tendsto_atTop (4 * b)] with N hQ hN
    have hQ' : (1 / 4 : ℝ) * cutoffLog N ≤ S N :=
      (le_div_iff₀ (cutoffLog_pos N)).1 hQ.le
    linarith
  have hO : S =O[atTop] cutoffLog := by
    refine isBigO_iff.2 ⟨1, ?_⟩
    filter_upwards [(tendsto_order.1 sqrtAbelKernel_log_mean).2 1 (by norm_num)] with N hN
    have hNonneg : 0 ≤ S N := Finset.sum_nonneg fun j _ => sqrtAbelKernel_nonneg j
    rw [Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg (cutoffLog_pos N).le, one_mul]
    exact ((div_lt_iff₀ (cutoffLog_pos N)).1 hN).le.trans_eq (one_mul _)
  have hSum := (hE.sum_range sqrtAbelKernel_nonneg hS).trans_isBigO hO
  have hDiv : (fun N => (cutoffLog N)⁻¹ • ∑ j ∈ Finset.range N, E j) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    apply ((isBigO_refl (fun N => (cutoffLog N)⁻¹) atTop).smul_isLittleO hSum).congr'
      Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun N => by
      change (cutoffLog N)⁻¹ • cutoffLog N = 1
      rw [smul_eq_mul, inv_mul_cancel₀ (cutoffLog_pos N).ne']
  have hDivLim := (isLittleO_one_iff ℝ).1 hDiv
  have hConst : Tendsto (fun N => (S N / cutoffLog N) • A) atTop (𝓝 ((1 / 2 : ℝ) • A)) :=
    sqrtAbelKernel_log_mean.smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (𝓝 A))
  have hBoth : Tendsto (fun N => (cutoffLog N)⁻¹ • (∑ j ∈ Finset.range N, E j) +
      (S N / cutoffLog N) • A) atTop (𝓝 ((1 / 2 : ℝ) • A)) := by
    simpa only [zero_add] using hDivLim.add hConst
  refine hBoth.congr fun N => ?_
  have hSplit : (∑ j ∈ Finset.range N, sqrtAbelKernel j • u j) =
      (∑ j ∈ Finset.range N, E j) + S N • A := by
    unfold S
    rw [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold E
    rw [← smul_add, sub_add_cancel]
  rw [hSplit, smul_add, smul_smul]
  rw [div_eq_mul_inv, mul_comm (S N)]

theorem normalized_abel_sum_log_limit (g : ℕ → ℂ) {A : ℂ}
    (hg : Tendsto (fun N => (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), g j)
      atTop (𝓝 A)) :
    Tendsto (fun N => (cutoffLog N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), (squareRootScale j)⁻¹ • g j)
      atTop (𝓝 ((1 / 2 : ℝ) • A)) := by
  let U (N : ℕ) := (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), g j
  have hAbel (N : ℕ) :
      (∑ j ∈ Finset.range (N + 1), (squareRootScale j)⁻¹ • g j) =
        U N + ∑ j ∈ Finset.range N, sqrtAbelKernel j • U j := by
    have hp := Finset.sum_range_by_parts (fun j => (squareRootScale j)⁻¹) g (N + 1)
    simp only [Nat.add_sub_cancel] at hp
    rw [hp, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    apply congrArg (fun v : ℂ => U N + v)
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold U
    rw [← neg_smul, smul_smul]
    have hne (i : ℕ) : squareRootScale i ≠ 0 :=
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos i))).ne'
    have he : -((squareRootScale (j + 1))⁻¹ - (squareRootScale j)⁻¹) =
        sqrtAbelKernel j * (squareRootScale j)⁻¹ := by
      unfold sqrtAbelKernel
      field_simp [hne j, hne (j + 1)] <;> ring
    rw [he]
  have hi : Tendsto (fun N => (cutoffLog N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp cutoffLog_tendsto_atTop
  have hz : Tendsto (fun N => (cutoffLog N)⁻¹ • U N) atTop (𝓝 0) := by
    simpa only [zero_smul] using hi.smul hg
  have hw := sqrtAbel_weighted_mean U hg
  have h : Tendsto (fun N => (cutoffLog N)⁻¹ • U N +
      (cutoffLog N)⁻¹ • (∑ j ∈ Finset.range N, sqrtAbelKernel j • U j))
      atTop (𝓝 ((1 / 2 : ℝ) • A)) := by
    simpa only [zero_add] using hz.add hw
  exact h.congr fun N => by rw [hAbel, smul_add]

end
end ManuscriptAudit.Paper8SqrtAbelLogTransfer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SqrtAbelLogTransfer.sqrtAbel_weighted_mean,
      ``ManuscriptAudit.Paper8SqrtAbelLogTransfer.normalized_abel_sum_log_limit] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
