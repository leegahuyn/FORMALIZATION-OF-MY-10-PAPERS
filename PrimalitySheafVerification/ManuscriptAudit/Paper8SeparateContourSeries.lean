import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourSingle
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourAnalyticDifference

/-!
# Exact convergence reduction for the two separate signed contour series

Both separate series differ from the same m = 0 series by absolutely
summable terms on the explicit q-disk. The native criterion keeps that
common signed arithmetic series as an explicit remaining condition.
-/

namespace ManuscriptAudit.Paper8SeparateContourSeries

open Filter
open scoped Topology
open Paper8LocalContour (root)
open Paper8ContourResidueWeights (prefactor residueWeight)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8ContourGammaRemainder (bound bound_nonneg)
open Paper8ContourSignedDominance (decay decay_nonneg)
open Paper8FixedContourDifference (phiAtQ difference)
open Paper8FixedContourSingle (common singleRemainder phi_eq_common_add_remainder singleRemainder_norm_le)
open Paper8ContourDifferenceTerms (term root_power_norm norm_weighted_le)
open Paper8ContourAnalyticDifference (normalizedDifference outerDifference absolute_summability_on_disk)

noncomputable section

private def sumKernel (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (F : ℂ → ℂ) : ℂ :=
  prefactor k * ∑ d ∈ S k, residueWeight k d * F (root k ^ (d.val : ℤ))

def commonTerm (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => common k ζ q)

def separateTerm (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => phiAtQ α β k ζ q)

def remainderTerm (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (q : ℂ) : ℂ :=
  sumKernel S k (fun ζ => singleRemainder α β k ζ q)

def singleOuterSeries (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (q : ℂ) : ℂ :=
  1 + (Real.pi : ℂ) * q * (∑' n : ℕ, separateTerm α β S (n + 1) q)

theorem separate_eq_common_add_remainder (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    separateTerm α β S k q = commonTerm S k q + remainderTerm α β S k q := by
  unfold separateTerm commonTerm remainderTerm sumKernel
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [phi_eq_common_add_remainder α hβ hβ' hk (root_power_norm k d) hq, mul_add]

theorem remainder_absolutely_summable {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 4) : Summable (fun n : ℕ => ‖remainderTerm α β S (n + 1) q‖) := by
  have hs : Summable (fun n : ℕ => decay (n + 1)) := by
    exact (summable_nat_add_iff 1).mp
      (Paper8ContourSignedDominance.decay_tail_summable 2 (by decide))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (hs.mul_left (8 * fixedRadius * bound fixedRadius))
  intro n
  have hn : 0 < n + 1 := Nat.succ_pos n
  have hc : 0 ≤ (4 * fixedRadius * bound fixedRadius) * decay (n + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le) (bound_nonneg fixedRadius_pos))
      (decay_nonneg _)
  have h := norm_weighted_le hn (S (n + 1))
    (fun d => singleRemainder α β (n + 1) (root (n + 1) ^ (d.val : ℤ)) q) hc
      (fun d _ => singleRemainder_norm_le hα hα' hβ hβ' hn (root_power_norm (n + 1) d) hq)
  change ‖prefactor (n + 1) * ∑ d ∈ S (n + 1), residueWeight (n + 1) d *
    singleRemainder α β (n + 1) (root (n + 1) ^ (d.val : ℤ)) q‖ ≤ _
  convert h using 1 <;> ring

theorem separate_summable_iff_common {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24) (hβ : 0 ≤ β)
    (hβ' : β ≤ 24) (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    Summable (fun n : ℕ => separateTerm α β S (n + 1) q) ↔
      Summable (fun n : ℕ => commonTerm S (n + 1) q) := by
  have hTail := (remainder_absolutely_summable hα hα' hβ hβ' S hq).of_norm
  have hTerm (n : ℕ) := separate_eq_common_add_remainder α hβ hβ' S (Nat.succ_pos n) hq
  constructor
  · intro h
    refine (h.sub hTail).congr fun n => ?_
    rw [hTerm]
    ring
  · intro h
    exact (h.add hTail).congr fun n => (hTerm n).symm

private theorem term_eq_separate_sub (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (q : ℂ) :
    term S k q = separateTerm 23 24 S k q - separateTerm (2 / 3) 16 S k q := by
  unfold term separateTerm sumKernel difference
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem outer_difference_eq_of_common_summable (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) (hCommon : Summable (fun n : ℕ => commonTerm S (n + 1) q)) :
    outerDifference S q = singleOuterSeries 23 24 S q - singleOuterSeries (2 / 3) 16 S q := by
  have hPrimary := (separate_summable_iff_common (α := 23) (β := 24)
    (by norm_num) (by norm_num) (by norm_num) le_rfl S hq).2 hCommon
  have hLiteral := (separate_summable_iff_common (α := 2 / 3) (β := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) S hq).2 hCommon
  have hSum : normalizedDifference S q =
      (∑' n : ℕ, separateTerm 23 24 S (n + 1) q) - ∑' n : ℕ, separateTerm (2 / 3) 16 S (n + 1) q := by
    unfold normalizedDifference
    rw [← hPrimary.tsum_sub hLiteral]
    exact tsum_congr (fun n => term_eq_separate_sub S (n + 1) q)
  rw [outerDifference, hSum]
  unfold singleOuterSeries
  ring

def orderedPartialSum (f : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, f n

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

theorem outer_difference_eq_of_ordered_limits (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 4) {LP LL : ℂ}
    (hPrimary : Tendsto (orderedPartialSum (fun n => separateTerm 23 24 S (n + 1) q)) atTop (𝓝 LP))
    (hLiteral : Tendsto (orderedPartialSum (fun n => separateTerm (2 / 3) 16 S (n + 1) q)) atTop (𝓝 LL)) :
    outerDifference S q = (1 + (Real.pi : ℂ) * q * LP) - (1 + (Real.pi : ℂ) * q * LL) := by
  have hNative : Tendsto (orderedPartialSum (fun n => term S (n + 1) q)) atTop
      (𝓝 (normalizedDifference S q)) :=
    (absolute_summability_on_disk S hq).of_norm.tendsto_sum_tsum_nat
  have hOrdered : Tendsto (orderedPartialSum (fun n => term S (n + 1) q)) atTop (𝓝 (LP - LL)) := by
    refine (hPrimary.sub hLiteral).congr fun N => ?_
    change orderedPartialSum (fun n => separateTerm 23 24 S (n + 1) q) N -
      orderedPartialSum (fun n => separateTerm (2 / 3) 16 S (n + 1) q) N =
        orderedPartialSum (fun n => term S (n + 1) q) N
    unfold orderedPartialSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => (term_eq_separate_sub S (n + 1) q).symm)
  rw [outerDifference, tendsto_nhds_unique hNative hOrdered]
  ring

end
end ManuscriptAudit.Paper8SeparateContourSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SeparateContourSeries.separate_eq_common_add_remainder,
      ``ManuscriptAudit.Paper8SeparateContourSeries.remainder_absolutely_summable,
      ``ManuscriptAudit.Paper8SeparateContourSeries.separate_summable_iff_common,
      ``ManuscriptAudit.Paper8SeparateContourSeries.outer_difference_eq_of_common_summable,
      ``ManuscriptAudit.Paper8SeparateContourSeries.separate_ordered_limit_iff_common,
      ``ManuscriptAudit.Paper8SeparateContourSeries.separate_ordered_convergence_iff_common,
      ``ManuscriptAudit.Paper8SeparateContourSeries.outer_difference_eq_of_ordered_limits] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
