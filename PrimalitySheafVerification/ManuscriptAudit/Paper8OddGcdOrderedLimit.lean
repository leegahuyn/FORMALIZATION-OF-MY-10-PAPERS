import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Tannery
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdResiduePhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparateReciprocalContourSeries

/-!
# Ordered convergence of the odd-gcd rescaling once the reduced series converges

The odd-gcd weight is (-1)^((g-1)/2) g^(-3/2), including the
Jacobi/Gamma coefficient scaling. An absolutely summable family of
such rescalings preserves ordinary convergence of the reduced common
series. This does not treat the distinct even-gcd subfamilies.
-/

namespace ManuscriptAudit.Paper8OddGcdOrderedLimit

open Filter
open scoped Topology
open Paper8ContourGammaSeries (coefficient scale)
open Paper8OddGcdResiduePhase (oddFactorSign)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8SeparateReciprocalContourSeries (commonTerm)
open Paper8ContourResidueWeights (reducedResidues)

noncomputable section

def oddScale (g : ℕ) : ℂ :=
  if Odd g then oddFactorSign g * ((1 / (g : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) else 0

theorem coefficient_zero_rescale {g k : ℕ} (hg : 0 < g) (hk : 0 < k) :
    coefficient (g * k) 0 = (1 / (g : ℝ) ^ (1 / 2 : ℝ)) * coefficient k 0 := by
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hg
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hScale : scale (g * k) = (1 / (g : ℝ)) * scale k := by
    unfold scale
    rw [Nat.cast_mul]
    field_simp [hgR.ne', hkR.ne'] <;> ring
  simp only [coefficient, Nat.cast_zero, mul_zero, zero_add, hScale]
  have hScaleNonneg : 0 ≤ scale k := by unfold scale; positivity
  rw [Real.mul_rpow (by positivity) hScaleNonneg, Real.div_rpow zero_le_one hgR.le,
    Real.one_rpow]
  ring

theorem odd_prefactor_coefficient_rescale {g k : ℕ} (hg : Odd g) (hk : 0 < k) :
    (oddFactorSign g / (g : ℂ)) * (coefficient (g * k) 0 : ℂ) =
      oddScale g * (coefficient k 0 : ℂ) := by
  have hgn : 0 < g := by obtain ⟨m, hm⟩ := hg; omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hgn
  have hPow : (g : ℝ) ^ (3 / 2 : ℝ) = (g : ℝ) * (g : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hgR, Real.rpow_one]
  have h : coefficient (g * k) 0 / (g : ℝ) =
      (1 / (g : ℝ) ^ (3 / 2 : ℝ)) * coefficient k 0 := by
    rw [coefficient_zero_rescale hgn hk, hPow]
    have hp : (g : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hgR _).ne'
    field_simp [hgR.ne', hp] <;> ring
  calc
    _ = oddFactorSign g * ((coefficient (g * k) 0 / (g : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by
      rw [h, oddScale, if_pos hg]
      push_cast
      ring

theorem oddScale_norm_le (g : ℕ) : ‖oddScale g‖ ≤ 1 / (g : ℝ) ^ (3 / 2 : ℝ) := by
  have h : 0 ≤ 1 / (g : ℝ) ^ (3 / 2 : ℝ) := by positivity
  by_cases hg : Odd g
  · rw [oddScale, if_pos hg, norm_mul, oddFactorSign, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg h] <;> exact le_rfl
  · rw [oddScale, if_neg hg, norm_zero]
    exact h

theorem oddScale_norm_summable : Summable (fun n : ℕ => ‖oddScale (n + 1)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => oddScale_norm_le (n + 1))
    ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by norm_num)))

private theorem nat_div_tendsto (n : ℕ) : Tendsto (fun N : ℕ => N / (n + 1)) atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  filter_upwards [eventually_ge_atTop (m * (n + 1))] with N hN
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos n)).2 hN

theorem weighted_divided_partial_limits (f w : ℕ → ℂ) {L : ℂ}
    (hf : Tendsto f atTop (𝓝 L)) (hw : Summable (fun n : ℕ => ‖w n‖)) :
    Tendsto (fun N => ∑' n : ℕ, w n * f (N / (n + 1))) atTop
      (𝓝 (∑' n : ℕ, w n * L)) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto f hf).exists_norm_le
  apply tendsto_tsum_of_dominated_convergence (hw.mul_right C)
  · intro n
    have h := hf.comp (nat_div_tendsto n)
    exact tendsto_const_nhds.mul h
  · exact Filter.Eventually.of_forall (fun N n => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ ⟨N / (n + 1), rfl⟩) (norm_nonneg _))

theorem odd_divided_sum_eq_finite (f : ℕ → ℂ) (N : ℕ) :
    (∑' n : ℕ, oddScale (n + 1) * orderedPartialSum f (N / (n + 1))) =
      ∑ n ∈ Finset.range N, oddScale (n + 1) * orderedPartialSum f (N / (n + 1)) := by
  apply tsum_eq_sum
  intro n hn
  have h : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le h), orderedPartialSum, Finset.range_zero, Finset.sum_empty,
    mul_zero]

theorem odd_part_ordered_limit (Q : ℂ) {L : ℂ}
    (hL : Tendsto (orderedPartialSum (fun k => commonTerm reducedResidues (k + 1) Q)) atTop (𝓝 L)) :
    Tendsto (fun N => ∑' n : ℕ, oddScale (n + 1) *
      orderedPartialSum (fun k => commonTerm reducedResidues (k + 1) Q) (N / (n + 1))) atTop
      (𝓝 (∑' n : ℕ, oddScale (n + 1) * L)) :=
  weighted_divided_partial_limits _ _ hL oddScale_norm_summable

end
end ManuscriptAudit.Paper8OddGcdOrderedLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.coefficient_zero_rescale,
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.odd_prefactor_coefficient_rescale,
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.oddScale_norm_summable,
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.weighted_divided_partial_limits,
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.odd_divided_sum_eq_finite,
      ``ManuscriptAudit.Paper8OddGcdOrderedLimit.odd_part_ordered_limit] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
