import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdOrderedLimit

/-!
# Denominator weights of the literal signed even sector

A finite exchange of the half-gcd and denominator indices isolates
each denominator's signed weight. Its norm is bounded uniformly in
the cutoff and the denominator by the positive h^(-3/2) series.
-/

namespace ManuscriptAudit.Paper8EvenDenominatorWeights

open Filter
open scoped Topology
open Paper8EvenGcdArithmeticRows (even_residue_class_fourier_rescale)
open Paper8EvenGcdOrderedLimit (evenSectorCutoff evenWeight evenWeight_norm
  evenWeight_norm_summable unshiftedCoefficient)

noncomputable section

def evenDenominatorWeight (N D : ℕ) : ℂ :=
  ∑ h ∈ Finset.range (N / D), evenWeight (h + 1) D

private theorem sum_div_cutoff_cond (N a : ℕ) (ha : 0 < a) (f : ℕ → ℂ) :
    (∑ d ∈ Finset.range (N / a), f d) =
      ∑ d ∈ Finset.range N, if (d + 1) * a ≤ N then f d else 0 := by
  have hEq : Finset.range (N / a) =
      (Finset.range N).filter (fun d => (d + 1) * a ≤ N) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hd
      exact ⟨hd.trans_le (Nat.div_le_self N a),
        (Nat.le_div_iff_mul_le ha).1 (Nat.succ_le_of_lt hd)⟩
    · rintro ⟨_, hd⟩
      exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le ha).2 hd)
  rw [hEq, Finset.sum_filter]

theorem even_cutoff_eq_denominator_weights (N n : ℕ) :
    evenSectorCutoff N n =
      ∑ d ∈ Finset.range N, evenDenominatorWeight N (d + 1) * unshiftedCoefficient (d + 1) n := by
  let f (h d : ℕ) : ℂ := evenWeight (h + 1) (d + 1) * unshiftedCoefficient (d + 1) n
  calc
    _ = ∑ h ∈ Finset.range N, ∑ d ∈ Finset.range (N / (h + 1)), f h d := by
      unfold evenSectorCutoff
      exact Finset.sum_congr rfl (fun h _ =>
        Finset.sum_congr rfl (fun d _ =>
          even_residue_class_fourier_rescale (Nat.succ_pos h) (Nat.succ_pos d) n))
    _ = ∑ h ∈ Finset.range N, ∑ d ∈ Finset.range N,
        if (d + 1) * (h + 1) ≤ N then f h d else 0 :=
      Finset.sum_congr rfl (fun h _ => sum_div_cutoff_cond N (h + 1) (Nat.succ_pos h) (f h))
    _ = ∑ d ∈ Finset.range N, ∑ h ∈ Finset.range N,
        if (d + 1) * (h + 1) ≤ N then f h d else 0 := Finset.sum_comm
    _ = ∑ d ∈ Finset.range N, ∑ h ∈ Finset.range (N / (d + 1)), f h d := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [sum_div_cutoff_cond N (d + 1) (Nat.succ_pos d)]
      exact Finset.sum_congr rfl (fun h _ => by rw [Nat.mul_comm (d + 1) (h + 1)])
    _ = _ := by
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold evenDenominatorWeight f
      rw [Finset.sum_mul]

theorem even_denominator_weight_uniform (N D : ℕ) :
    ‖evenDenominatorWeight N D‖ ≤ ∑' h : ℕ, 1 / ((h + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  have hs : Summable (fun h : ℕ => 1 / ((h + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
    simpa only [evenWeight_norm] using evenWeight_norm_summable D
  calc
    _ ≤ ∑ h ∈ Finset.range (N / D), ‖evenWeight (h + 1) D‖ := norm_sum_le _ _
    _ ≤ _ := by
      simp only [evenWeight_norm]
      exact hs.sum_le_tsum _ (fun _ _ => by positivity)

theorem even_denominator_weight_tendsto {D : ℕ} (hD : 0 < D) :
    Tendsto (fun N => evenDenominatorWeight N D) atTop
      (𝓝 (∑' h : ℕ, evenWeight (h + 1) D)) := by
  have hDiv : Tendsto (fun N : ℕ => N / D) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b * D)] with N hN
    exact (Nat.le_div_iff_mul_le hD).2 hN
  exact ((evenWeight_norm_summable D).of_norm.tendsto_sum_tsum_nat).comp hDiv

end
end ManuscriptAudit.Paper8EvenDenominatorWeights

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenDenominatorWeights.even_cutoff_eq_denominator_weights,
      ``ManuscriptAudit.Paper8EvenDenominatorWeights.even_denominator_weight_uniform,
      ``ManuscriptAudit.Paper8EvenDenominatorWeights.even_denominator_weight_tendsto] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
