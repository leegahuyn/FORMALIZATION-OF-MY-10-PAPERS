import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8LowerContourAnalyticDifference
import PrimalitySheafVerification.ManuscriptAudit.Paper8LowerContourParameterLink
import PrimalitySheafVerification.ManuscriptAudit.Paper8LiteralContourLimits

/-!
# Distinct lower-half-plane ordered limits for the two contour kernels

The difference of the original ordered partial sums has a nonzero
limit near the cusp in the lower half plane, in both residue readings.
Any pair of separate convergent sums must therefore have distinct limits.
-/

namespace ManuscriptAudit.Paper8LowerContourLimits

open Filter Metric Set
open scoped Topology
open Paper8HolomorphicPartPhase (qParameter)
open Paper8ContourResidueWeights (prefactor residueWeight reducedResidues)
open Paper8LocalContour (root phi)
open Paper8FixedContourDifference (phiAtQ)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8LiteralContourLimits (printedScalar printedScalar_eq printedOuterPartialSum)
open Paper8ReciprocalContourAtZero (inverseNomeTerm)
open Paper8LowerContourParameterLink (nome_mul_phi_eq_inverse_nome)
open Paper8ContourParameterLink (positive_real_nome_has_upper_half_plane_parameter)
open Paper8LowerContourAnalyticDifference (normalizedDifference outerDifference absolute_summability_on_disk
  reduced_outerDifference_real_positive_near_zero all_outerDifference_real_positive_near_zero)

noncomputable section

private theorem signed_sum_difference (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k)
    {z : ℂ} (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    prefactor k * (∑ d ∈ S k, printedScalar z k d * phi 23 24 k (d.val : ℤ) z) -
      prefactor k * (∑ d ∈ S k, printedScalar z k d * phi (2 / 3) 16 k (d.val : ℤ) z) =
        inverseNomeTerm S k (qParameter (-z)) := by
  unfold inverseNomeTerm
  rw [← mul_sub, ← Finset.sum_sub_distrib, neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  apply congrArg (fun w : ℂ => prefactor k * w)
  refine Finset.sum_congr rfl fun d _ => ?_
  change printedScalar z k d * phi 23 24 k (d.val : ℤ) z -
      printedScalar z k d * phi (2 / 3) 16 k (d.val : ℤ) z =
    -(residueWeight k d * (root k ^ (d.val : ℤ))⁻¹ *
      (phiAtQ (-1) (-24) k (root k ^ (d.val : ℤ))⁻¹ (qParameter (-z)) -
        phiAtQ (-46 / 3) (-16) k (root k ^ (d.val : ℤ))⁻¹ (qParameter (-z))))
  have hP : (23 : ℝ) - 24 = -1 := by norm_num
  have hL : (2 / 3 : ℝ) - 16 = -46 / 3 := by norm_num
  rw [printedScalar_eq, mul_assoc (residueWeight k d) (qParameter z),
    mul_assoc (residueWeight k d) (qParameter z),
    nome_mul_phi_eq_inverse_nome 23 (by norm_num) le_rfl hk (d.val : ℤ) hz hq,
    nome_mul_phi_eq_inverse_nome (2 / 3) (by norm_num) (by norm_num) hk (d.val : ℤ) hz hq,
    hP, hL]
  ring

theorem printed_partial_sum_difference (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ}
    (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) (N : ℕ) :
    printedOuterPartialSum 23 24 S z N - printedOuterPartialSum (2 / 3) 16 S z N =
      (Real.pi : ℂ) * orderedPartialSum (fun n => inverseNomeTerm S (n + 1) (qParameter (-z))) N := by
  let P (n : ℕ) := prefactor (n + 1) * (∑ d ∈ S (n + 1),
    printedScalar z (n + 1) d * phi 23 24 (n + 1) (d.val : ℤ) z)
  let L (n : ℕ) := prefactor (n + 1) * (∑ d ∈ S (n + 1),
    printedScalar z (n + 1) d * phi (2 / 3) 16 (n + 1) (d.val : ℤ) z)
  change (1 + (Real.pi : ℂ) * (∑ n ∈ Finset.range N, P n)) -
    (1 + (Real.pi : ℂ) * (∑ n ∈ Finset.range N, L n)) =
      (Real.pi : ℂ) * (∑ n ∈ Finset.range N, inverseNomeTerm S (n + 1) (qParameter (-z)))
  calc
    _ = (Real.pi : ℂ) * ((∑ n ∈ Finset.range N, P n) - ∑ n ∈ Finset.range N, L n) := by ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply congrArg (fun w : ℂ => (Real.pi : ℂ) * w)
      exact Finset.sum_congr rfl (fun n _ => signed_sum_difference S (Nat.succ_pos n) hz hq)

theorem printed_difference_tendsto (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ}
    (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    Tendsto (fun N => printedOuterPartialSum 23 24 S z N - printedOuterPartialSum (2 / 3) 16 S z N)
      atTop (𝓝 (outerDifference S (qParameter (-z)))) := by
  have h : Tendsto (orderedPartialSum (fun n => inverseNomeTerm S (n + 1) (qParameter (-z)))) atTop
      (𝓝 (normalizedDifference S (qParameter (-z)))) :=
    (absolute_summability_on_disk S hq).of_norm.tendsto_sum_tsum_nat
  have hC : Tendsto (fun _ : ℕ => (Real.pi : ℂ)) atTop (𝓝 (Real.pi : ℂ)) := tendsto_const_nhds
  change Tendsto _ atTop (𝓝 ((Real.pi : ℂ) * normalizedDifference S (qParameter (-z))))
  exact (hC.mul h).congr (fun N => (printed_partial_sum_difference S hz hq N).symm)

theorem no_common_printed_ordered_limit (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ}
    (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) (hDiff : outerDifference S (qParameter (-z)) ≠ 0) :
    ¬ ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 S z) atTop (𝓝 L) ∧
      Tendsto (printedOuterPartialSum (2 / 3) 16 S z) atTop (𝓝 L) := by
  rintro ⟨L, hP, hL⟩
  have hEq := tendsto_nhds_unique (printed_difference_tendsto S hz hq) (hP.sub hL)
  exact hDiff (hEq.trans (sub_self L))

theorem no_common_printed_ordered_limit_at_lower_half_plane_parameters :
    ∃ r : ℝ, 0 < r ∧ ∀ Q ∈ Ioo (0 : ℝ) r, ∃ z : ℂ, z.im < 0 ∧ qParameter (-z) = (Q : ℂ) ∧
      (¬ ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 reducedResidues z) atTop (𝓝 L) ∧
        Tendsto (printedOuterPartialSum (2 / 3) 16 reducedResidues z) atTop (𝓝 L)) ∧
      (¬ ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 (fun _ => Finset.univ) z) atTop (𝓝 L) ∧
        Tendsto (printedOuterPartialSum (2 / 3) 16 (fun _ => Finset.univ) z) atTop (𝓝 L)) := by
  obtain ⟨rP, hrP, hP4, hP⟩ := reduced_outerDifference_real_positive_near_zero
  obtain ⟨rL, hrL, _, hL⟩ := all_outerDifference_real_positive_near_zero
  refine ⟨min rP rL, lt_min hrP hrL, ?_⟩
  intro Q hQ
  have hQP : Q < rP := hQ.2.trans_le (min_le_left _ _)
  have hQL : Q < rL := hQ.2.trans_le (min_le_right _ _)
  have hQ4 : Q ≤ 1 / 4 := hQP.le.trans hP4
  obtain ⟨w, hw, hNome⟩ :=
    positive_real_nome_has_upper_half_plane_parameter hQ.1 (hQ4.trans_lt (by norm_num))
  let z := -w
  have hz : z.im < 0 := by simpa only [z, Complex.neg_im, neg_neg, neg_lt_zero] using hw
  have hZ : qParameter (-z) = (Q : ℂ) := by simpa only [z, neg_neg] using hNome
  have hQN : ‖qParameter (-z)‖ = Q := by rw [hZ, Complex.norm_real, Real.norm_of_nonneg hQ.1.le]
  have hBP : qParameter (-z) ∈ ball (0 : ℂ) rP := by rw [mem_ball, dist_zero_right, hQN]; exact hQP
  have hBL : qParameter (-z) ∈ ball (0 : ℂ) rL := by rw [mem_ball, dist_zero_right, hQN]; exact hQL
  have hZ4 : ‖qParameter (-z)‖ ≤ 1 / 4 := by rw [hQN]; exact hQ4
  refine ⟨z, hz, hZ, no_common_printed_ordered_limit reducedResidues hz hZ4 ?_,
    no_common_printed_ordered_limit (fun _ => Finset.univ) hz hZ4 ?_⟩
  · intro h
    have hh := hP _ hBP
    rw [h, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  · intro h
    have hh := hL _ hBL
    rw [h, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh

end
end ManuscriptAudit.Paper8LowerContourLimits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LowerContourLimits.printed_partial_sum_difference,
      ``ManuscriptAudit.Paper8LowerContourLimits.printed_difference_tendsto,
      ``ManuscriptAudit.Paper8LowerContourLimits.no_common_printed_ordered_limit_at_lower_half_plane_parameters] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
