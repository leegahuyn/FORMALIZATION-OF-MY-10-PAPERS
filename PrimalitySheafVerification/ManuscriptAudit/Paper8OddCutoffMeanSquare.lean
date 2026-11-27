import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.PiL2
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueModeConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReducedCutoffMeanSquare

/-! The odd divisor cutoff preserves the uniform finite frequency mean-square bound. -/

namespace ManuscriptAudit.Paper8OddCutoffMeanSquare

open Paper8ContourResidueWeights (reducedResidues)
open Paper8ContourGammaSeries (coefficient)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8ReciprocalCommonFourier (fourierCoefficient orderedFourierCoefficient)
open Paper8OddGcdOrderedLimit (oddScale oddScale_norm_summable odd_divided_sum_eq_finite)
open Paper8AllResidueModeConvergence (oddSectorCutoff odd_sector_cutoff_eq_tsum)
open Paper8ReducedCutoffMeanSquare (reduced_cutoff_frequency_average_bounded)

noncomputable section

private def sample (M : ℕ) : (ℕ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin M) :=
  (WithLp.linearEquiv 2 ℂ (Fin M → ℂ)).symm.toLinearMap.comp
    { toFun := fun f j => f j.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem sample_norm_sq (M : ℕ) (f : ℕ → ℂ) :
    ‖sample M f‖ ^ 2 = ∑ n ∈ Finset.range M, ‖f n‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin M, ‖f j.val‖ ^ 2) = _
  exact Fin.sum_univ_eq_sum_range _ _

private theorem sample_odd_sum (N M : ℕ) :
    sample M (fun n => oddSectorCutoff N n) =
      ∑ h ∈ Finset.range N, oddScale (h + 1) •
        sample M (fun n => orderedFourierCoefficient reducedResidues (N / (h + 1)) n) := by
  have he : (fun n => oddSectorCutoff N n) =
      ∑ h ∈ Finset.range N, oddScale (h + 1) •
        (fun n => orderedFourierCoefficient reducedResidues (N / (h + 1)) n) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [odd_sector_cutoff_eq_tsum]
    exact odd_divided_sum_eq_finite (fun k => fourierCoefficient reducedResidues (k + 1) n) N
  rw [he, map_sum]
  simp only [map_smul]

theorem odd_cutoff_frequency_average_bounded (N : ℕ) {M : ℕ} (hPos : 0 < M)
    (hM : ∀ k ∈ Finset.range N, 2 * (k + 1) ∣ M) :
    ((∑ n ∈ Finset.range M, ‖oddSectorCutoff N n‖ ^ 2) / (M : ℝ)) ≤
      (∑' h : ℕ, ‖oddScale (h + 1)‖)^2 *
        ((2 * (coefficient 1 0)^2) * ∑' j : ℕ, 1 / ((j + 1 : ℕ) : ℝ)^2) := by
  let C : ℝ := (2 * (coefficient 1 0)^2) * ∑' j : ℕ, 1 / ((j + 1 : ℕ) : ℝ)^2
  let W : ℝ := ∑' h : ℕ, ‖oddScale (h + 1)‖
  let R : ℝ := Real.sqrt ((M : ℝ) * C)
  let U (h : ℕ) : EuclideanSpace ℂ (Fin M) :=
    sample M (fun n => orderedFourierCoefficient reducedResidues (N / (h + 1)) n)
  have hm : 0 < (M : ℝ) := by exact_mod_cast hPos
  have hC : 0 ≤ C := mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)
  have hW : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hs (h : ℕ) : ‖U h‖ ≤ R := by
    have hN : N / (h + 1) ≤ N := Nat.div_le_self _ _
    have hCut := reduced_cutoff_frequency_average_bounded (N / (h + 1)) hPos
      (fun k hk => hM k (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hN)))
    have hSq : ‖U h‖ ^ 2 ≤ (M : ℝ) * C := by
      unfold U
      rw [sample_norm_sq]
      have hCut' : (∑ n ∈ Finset.range M,
          ‖orderedFourierCoefficient reducedResidues (N / (h + 1)) n‖ ^ 2) ≤ C * (M : ℝ) :=
        (div_le_iff₀ hm).mp hCut
      simpa only [mul_comm C (M : ℝ)] using hCut'
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg hm.le hC)).2 hSq
  have hBound : ‖sample M (fun n => oddSectorCutoff N n)‖ ≤ W * R := by
    rw [sample_odd_sum]
    calc
      _ ≤ ∑ h ∈ Finset.range N, ‖oddScale (h + 1) • U h‖ := norm_sum_le _ _
      _ = ∑ h ∈ Finset.range N, ‖oddScale (h + 1)‖ * ‖U h‖ :=
        Finset.sum_congr rfl (fun _ _ => norm_smul _ _)
      _ ≤ ∑ h ∈ Finset.range N, ‖oddScale (h + 1)‖ * R :=
        Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hs h) (norm_nonneg _))
      _ = (∑ h ∈ Finset.range N, ‖oddScale (h + 1)‖) * R := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (oddScale_norm_summable.sum_le_tsum _ (fun _ _ => norm_nonneg _)) hR
  have hSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hW hR)).2 hBound
  rw [sample_norm_sq, mul_pow, show R ^ 2 = (M : ℝ) * C from Real.sq_sqrt (mul_nonneg hm.le hC)] at hSq
  apply (div_le_iff₀ hm).2
  change (∑ n ∈ Finset.range M, ‖oddSectorCutoff N n‖ ^ 2) ≤ (W ^ 2 * C) * (M : ℝ)
  exact hSq.trans_eq (by ring)

end
end ManuscriptAudit.Paper8OddCutoffMeanSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8OddCutoffMeanSquare.odd_cutoff_frequency_average_bounded
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
