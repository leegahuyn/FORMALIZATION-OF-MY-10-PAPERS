import Lean.Util.CollectAxioms
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourMomentTerm

/-!
# The individual contour moments at q = 0 differ

The literal p. 335 and primary Rhoades kernels specialize at q = 0 to
the same aₖ(s) times exp((2/3)s) and exp(23s), respectively.
Their actual normalized circle integrals differ at every positive radius
and k. This calculation uses termwise Cauchy integration only.
https://arxiv.org/pdf/1111.1495
-/

namespace ManuscriptAudit.Paper8ContourMoment

open Filter Metric Set
open Paper8ContourGammaSeries (a term majorant coefficient_pos majorant_summable norm_term_le_majorant)
open Paper8ContourMomentTerm (weightedTerm coefficientMoment weightedTerm_circle_integral)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped Topology

noncomputable section

def atZero (α : ℝ) (k : ℕ) (r : ℝ) : ℂ :=
  periodCoefficient⁻¹ * circleIntegral (fun s : ℂ => a k s * Complex.exp ((α : ℂ) * s)) 0 r

private theorem sphere_norm_eq {r : ℝ} {s : ℂ} (hs : s ∈ sphere (0 : ℂ) r) : ‖s‖ = r := by
  simpa only [mem_sphere, dist_zero_right] using hs

private theorem norm_weightedTerm_le {k : ℕ} (hk : 0 < k) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (m : ℕ) {s : ℂ} (hs : s ∈ sphere (0 : ℂ) r) :
    ‖weightedTerm α k m s‖ ≤ majorant k r m * Real.exp (|α| * r) := by
  have hNorm := sphere_norm_eq hs
  have hExp : ‖Complex.exp ((α : ℂ) * s)‖ ≤ Real.exp (|α| * r) := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Real.exp_le_exp.mpr
    calc
      α * s.re ≤ |α * s.re| := le_abs_self _
      _ = |α| * |s.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm s).trans (le_of_eq hNorm)) (abs_nonneg α)
  rw [weightedTerm, norm_mul]
  have hMajorant : 0 ≤ majorant k r m := (div_pos (coefficient_pos hk m) (pow_pos hr _)).le
  exact mul_le_mul (norm_term_le_majorant hk hr hNorm.ge m) hExp (norm_nonneg _) hMajorant

private theorem weightedTerm_continuousOn (α : ℝ) (k m : ℕ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (weightedTerm α k m) (sphere (0 : ℂ) r) := by
  have hPow : ContinuousOn (fun s : ℂ => s ^ (m + 1)) (sphere (0 : ℂ) r) :=
    (continuous_id.pow (m + 1)).continuousOn
  have hTerm : ContinuousOn (term k m) (sphere (0 : ℂ) r) := by
    apply continuousOn_const.div hPow
    intro s hs
    exact pow_ne_zero _ (norm_pos_iff.mp (by simpa only [sphere_norm_eq hs] using hr))
  have hExp : Continuous (fun s : ℂ => Complex.exp ((α : ℂ) * s)) :=
    Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hTerm.mul hExp.continuousOn

theorem hasSum_atZero_re {k : ℕ} (hk : 0 < k) (α : ℝ) {r : ℝ} (hr : 0 < r) :
    HasSum (coefficientMoment α k) (atZero α k r).re := by
  have hMajorant := (majorant_summable hk hr).mul_right (Real.exp (|α| * r))
  have hUniform0 := HasSumUniformlyOn.of_norm_le_summable (f := weightedTerm α k)
    (s := sphere (0 : ℂ) r) hMajorant (fun m z hz => norm_weightedTerm_le hk α hr m hz)
  have hUniform : HasSumUniformlyOn (weightedTerm α k)
      (fun s : ℂ => a k s * Complex.exp ((α : ℂ) * s)) (sphere (0 : ℂ) r) := by
    refine hUniform0.congr_right fun s _ => ?_
    exact tsum_mul_right
  have hCont : ∀ᶠ S : Finset ℕ in atTop, ContinuousOn (fun s : ℂ => ∑ m ∈ S, weightedTerm α k m s)
      (sphere (0 : ℂ) r) :=
    Eventually.of_forall fun S => continuousOn_finsetSum S (fun m _ => weightedTerm_continuousOn α k m hr)
  have hLimit := hUniform.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hr.le hCont
  have hIntegral : HasSum (fun m => circleIntegral (weightedTerm α k m) 0 r)
      (circleIntegral (fun s : ℂ => a k s * Complex.exp ((α : ℂ) * s)) 0 r) := by
    refine hLimit.congr' (Eventually.of_forall fun S => ?_)
    exact circleIntegral.integral_fun_sum (fun m _ => (weightedTerm_continuousOn α k m hr).circleIntegrable hr.le)
  have hComplex : HasSum (fun m : ℕ => (coefficientMoment α k m : ℂ)) (atZero α k r) :=
    (hIntegral.mul_left periodCoefficient⁻¹).congr_fun fun m => (weightedTerm_circle_integral α k m hr).symm
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hComplex

theorem atZero_literal_lt_rhoades {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    (atZero (2 / 3) k r).re < (atZero 23 k r).re := by
  have hSum := (hasSum_atZero_re hk 23 hr).sub (hasSum_atZero_re hk (2 / 3) hr)
  have hNonneg (m : ℕ) : 0 ≤ coefficientMoment 23 k m - coefficientMoment (2 / 3) k m := by
    apply sub_nonneg.mpr
    unfold coefficientMoment
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (coefficient_pos hk m).le
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hOne : 0 < coefficientMoment 23 k 1 - coefficientMoment (2 / 3) k 1 := by
    apply sub_pos.mpr
    simp only [coefficientMoment, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact mul_lt_mul_of_pos_left (by norm_num) (coefficient_pos hk 1)
  have hTop := hSum.summable.sum_le_tsum ({1} : Finset ℕ) (fun m _ => hNonneg m)
  rw [hSum.tsum_eq, Finset.sum_singleton] at hTop
  exact sub_pos.mp (hOne.trans_le hTop)

end
end ManuscriptAudit.Paper8ContourMoment

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourMoment.hasSum_atZero_re,
      ``ManuscriptAudit.Paper8ContourMoment.atZero_literal_lt_rhoades] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
