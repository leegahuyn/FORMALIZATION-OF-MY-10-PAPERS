import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReflectedContourSingle
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparateContourSeries

/-!
# Exact separate convergence criterion in the inverse nome

The two lower-half-plane kernels have a shared signed Laurent term.
Their remaining terms are absolutely summable on the quarter disk.
-/

namespace ManuscriptAudit.Paper8SeparateReciprocalContourSeries

open Filter
open scoped Topology
open Paper8LocalContour (root)
open Paper8ContourResidueWeights (prefactor residueWeight)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8FixedContourSingle (common singleRemainder)
open Paper8ReflectedContourSingle (phi_eq_common_add_remainder singleRemainder_norm_le)
open Paper8FixedContourDifference (phiAtQ)
open Paper8ContourGammaRemainder (bound bound_nonneg)
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)
open Paper8ContourDifferenceTerms (root_power_norm norm_weighted_le)
open Paper8SeparateContourSeries (orderedPartialSum)

noncomputable section

def sumKernel (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (F : ℂ → ℂ) : ℂ :=
  -prefactor k * ∑ d ∈ S k, residueWeight k d * ((root k ^ (d.val : ℤ))⁻¹ *
    F (root k ^ (d.val : ℤ))⁻¹)

def commonTerm (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (Q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => common k ζ Q)

def separateTerm (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (Q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => phiAtQ (-α) (-β) k ζ Q)

def remainderTerm (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (Q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => singleRemainder (-α) (-β) k ζ Q)

private theorem inverse_root_norm (k : ℕ) (d : Fin (2 * k)) :
    ‖(root k ^ (d.val : ℤ))⁻¹‖ = 1 := by rw [norm_inv, root_power_norm, inv_one]

theorem separate_eq_common_add_remainder (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    separateTerm α β S k q = commonTerm S k q + remainderTerm α β S k q := by
  unfold separateTerm commonTerm remainderTerm sumKernel
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun w : ℂ => -prefactor k * w)
  refine Finset.sum_congr rfl fun d _ => ?_
  let ζ := (root k ^ (d.val : ℤ))⁻¹
  change residueWeight k d * (ζ * phiAtQ (-α) (-β) k ζ q) =
    residueWeight k d * (ζ * common k ζ q) +
      residueWeight k d * (ζ * singleRemainder (-α) (-β) k ζ q)
  rw [phi_eq_common_add_remainder α hβ hβ' hk (inverse_root_norm k d) hq, mul_add, mul_add]

theorem remainder_absolutely_summable {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 4) : Summable (fun n : ℕ => ‖remainderTerm α β S (n + 1) q‖) := by
  have hs : Summable (fun n : ℕ => decay (n + 1)) :=
    (summable_nat_add_iff 1).mp (decay_tail_summable 2 (by decide))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (hs.mul_left (8 * fixedRadius * bound fixedRadius))
  intro n
  let k := n + 1
  have hk : 0 < k := Nat.succ_pos n
  have hc : 0 ≤ (4 * fixedRadius * bound fixedRadius) * decay k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le) (bound_nonneg fixedRadius_pos))
      (decay_nonneg _)
  have h := norm_weighted_le hk (S k)
    (fun d => (root k ^ (d.val : ℤ))⁻¹ *
      singleRemainder (-α) (-β) k (root k ^ (d.val : ℤ))⁻¹ q) hc
    (fun d _ => by
      rw [norm_mul, inverse_root_norm, one_mul]
      exact singleRemainder_norm_le hα hα' hβ hβ' hk (inverse_root_norm k d) hq)
  change ‖remainderTerm α β S k q‖ ≤ (8 * fixedRadius * bound fixedRadius) * decay k
  rw [remainderTerm, sumKernel, neg_mul, norm_neg]
  exact h.trans_eq (by ring)

private theorem orderedPartialSum_separate (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) (N : ℕ) :
    orderedPartialSum (fun n => separateTerm α β S (n + 1) q) N =
      orderedPartialSum (fun n => commonTerm S (n + 1) q) N +
        orderedPartialSum (fun n => remainderTerm α β S (n + 1) q) N := by
  unfold orderedPartialSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun n _ => separate_eq_common_add_remainder α hβ hβ' S (Nat.succ_pos n) hq)

theorem separate_ordered_limit_iff_common {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24) (hβ : 0 ≤ β)
    (hβ' : β ≤ 24) (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4)
    (L : ℂ) :
    Tendsto (orderedPartialSum (fun n => separateTerm α β S (n + 1) q)) atTop (𝓝 L) ↔
      Tendsto (orderedPartialSum (fun n => commonTerm S (n + 1) q)) atTop
        (𝓝 (L - ∑' n : ℕ, remainderTerm α β S (n + 1) q)) := by
  let R := ∑' n : ℕ, remainderTerm α β S (n + 1) q
  have hTail : Tendsto (orderedPartialSum (fun n => remainderTerm α β S (n + 1) q)) atTop (𝓝 R) :=
    (remainder_absolutely_summable hα hα' hβ hβ' S hq).of_norm.tendsto_sum_tsum_nat
  have hEq := orderedPartialSum_separate α hβ hβ' S hq
  constructor
  · intro h
    refine (h.sub hTail).congr fun N => ?_
    change orderedPartialSum (fun n => separateTerm α β S (n + 1) q) N -
      orderedPartialSum (fun n => remainderTerm α β S (n + 1) q) N =
        orderedPartialSum (fun n => commonTerm S (n + 1) q) N
    rw [hEq N, add_sub_cancel_right]
  · intro h
    have hAdd := h.add hTail
    change Tendsto _ atTop (𝓝 ((L - R) + R)) at hAdd
    rw [sub_add_cancel] at hAdd
    exact hAdd.congr (fun N => (hEq N).symm)

theorem separate_ordered_convergence_iff_common {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    (∃ L : ℂ, Tendsto (orderedPartialSum (fun n => separateTerm α β S (n + 1) q)) atTop (𝓝 L)) ↔
      ∃ L : ℂ, Tendsto (orderedPartialSum (fun n => commonTerm S (n + 1) q)) atTop (𝓝 L) := by
  let R := ∑' n : ℕ, remainderTerm α β S (n + 1) q
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L - R, (separate_ordered_limit_iff_common hα hα' hβ hβ' S hq L).1 hL⟩
  · rintro ⟨L, hL⟩
    refine ⟨L + R, (separate_ordered_limit_iff_common hα hα' hβ hβ' S hq (L + R)).2 ?_⟩
    change Tendsto _ atTop (𝓝 (L + R - R))
    simpa only [add_sub_cancel_right] using hL

end
end ManuscriptAudit.Paper8SeparateReciprocalContourSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SeparateReciprocalContourSeries.separate_eq_common_add_remainder,
      ``ManuscriptAudit.Paper8SeparateReciprocalContourSeries.remainder_absolutely_summable,
      ``ManuscriptAudit.Paper8SeparateReciprocalContourSeries.separate_ordered_limit_iff_common,
      ``ManuscriptAudit.Paper8SeparateReciprocalContourSeries.separate_ordered_convergence_iff_common] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
