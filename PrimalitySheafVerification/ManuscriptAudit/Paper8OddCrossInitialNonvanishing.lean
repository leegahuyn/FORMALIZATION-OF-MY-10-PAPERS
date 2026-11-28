import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.Tannery
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossContinuationPole
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossFirstCoefficient

/-! The first cross modulus makes the actual Dirichlet series nonzero on its initial half-plane. -/

namespace ManuscriptAudit.Paper8OddCrossInitialNonvanishing

open Set Filter
open Paper8OddCrossCuspCutoff Paper8OddCrossFirstCoefficient Paper8OddCrossLaplaceTerm
open Paper8OddCrossDirichletLaplace Paper8OddCrossContinuationPole
open scoped Topology

noncomputable section

private def normalizedSummand (r : ℝ) (j : ℕ) : ℂ :=
  crossRaw j * (((j + 1 : ℕ) : ℂ) ^ (-(r : ℂ)))

private theorem normalizedSummand_tendsto (j : ℕ) :
    Tendsto (fun r => normalizedSummand r j) atTop
      (𝓝 (if j = 0 then (1 : ℂ) else 0)) := by
  by_cases hj : j = 0
  · subst j
    simpa [normalizedSummand, crossRaw_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1))
  rw [if_neg hj]
  have hK : 1 < ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < j + 1 by omega)
  have hK0 : 0 < ((j + 1 : ℕ) : ℝ) := zero_lt_one.trans hK
  have hK' : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hLog : 0 < Real.log ((j + 1 : ℕ) : ℝ) := Real.log_pos hK
  have hScale : Tendsto (fun r : ℝ => (-Real.log ((j + 1 : ℕ) : ℝ)) * r) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hLog)
  have hExp := Real.tendsto_exp_atBot.comp hScale
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hExp
  have hP : Tendsto (fun r : ℝ => (((j + 1 : ℕ) : ℂ) ^ (-(r : ℂ)))) atTop (𝓝 0) := by
    have hLogCast : (Real.log ((j + 1 : ℕ) : ℝ) : ℂ) = Complex.log ((j + 1 : ℕ) : ℂ) :=
      Complex.ofReal_log hK0.le
    simp_rw [Complex.cpow_def_of_ne_zero hK', ← hLogCast]
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, neg_mul, mul_neg] using hCast
  simpa only [normalizedSummand, mul_zero] using hP.const_mul (crossRaw j)

private theorem normalizedSummand_tsum_tendsto :
    Tendsto (fun r : ℝ => ∑' j : ℕ, normalizedSummand r j) atTop (𝓝 1) := by
  let majorant (j : ℕ) := ((j + 1 : ℕ) : ℝ) ^ (-2 : ℝ)
  have hSum : Summable majorant :=
    ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).congr (fun j => by
      unfold majorant
      rw [abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1), one_div,
        ← Real.rpow_neg (by positivity : 0 ≤ (j : ℝ) + 1), Nat.cast_add, Nat.cast_one])
  have hNorm : ∀ᶠ r : ℝ in atTop, ∀ j, ‖normalizedSummand r j‖ ≤ majorant j := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    intro j
    have hK : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 1 by omega)
    have hK0 : 0 < ((j + 1 : ℕ) : ℝ) := zero_lt_one.trans_le hK
    unfold normalizedSummand majorant
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hK0, Complex.neg_re, Complex.ofReal_re]
    exact (mul_le_of_le_one_left (by positivity) (norm_crossRaw_le_one j)).trans
      (Real.rpow_le_rpow_of_exponent_le hK (neg_le_neg hr))
  have hT := tendsto_tsum_of_dominated_convergence hSum normalizedSummand_tendsto hNorm
  have hG : (∑' j : ℕ, if j = 0 then (1 : ℂ) else 0) = 1 := by
    rw [tsum_eq_sum (s := ({0} : Finset ℕ))]
    · simp
    · intro j hj
      have hj' : j ≠ 0 := by simpa only [Finset.mem_singleton] using hj
      simp only [if_neg hj']
  rwa [hG] at hT

theorem crossShiftedDirichletSeries_first_modulus_limit :
    Tendsto (fun r : ℝ => (2 : ℂ) ^ ((r : ℂ) + 1) * crossShiftedDirichletSeries (r : ℂ))
      atTop (𝓝 1) := by
  refine normalizedSummand_tsum_tendsto.congr' (Eventually.of_forall fun r => ?_)
  unfold crossShiftedDirichletSeries
  simp_rw [oddCrossZetaTerm_eq_shifted]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
    add_neg_cancel, Complex.cpow_zero, one_mul] <;> rfl

theorem crossShiftedDirichletSeries_eventually_nonzero :
    ∀ᶠ r : ℝ in atTop, crossShiftedDirichletSeries (r : ℂ) ≠ 0 := by
  have hNear := (Metric.tendsto_nhds.1 crossShiftedDirichletSeries_first_modulus_limit) 1 zero_lt_one
  filter_upwards [hNear] with r hr
  intro hZero
  rw [hZero, mul_zero] at hr
  simpa [dist_eq_norm] using hr

end
end ManuscriptAudit.Paper8OddCrossInitialNonvanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossInitialNonvanishing.crossShiftedDirichletSeries_first_modulus_limit,
      ``ManuscriptAudit.Paper8OddCrossInitialNonvanishing.crossShiftedDirichletSeries_eventually_nonzero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
