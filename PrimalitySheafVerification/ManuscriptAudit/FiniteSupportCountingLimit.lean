import Lean.Util.CollectAxioms
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Removing a fixed finite set from actual counting sets changes any
normalized limiting proportion by zero when the denominator diverges. -/

namespace ManuscriptAudit.FiniteSupportCountingLimit

open Filter Topology

variable {α ι : Type*} [DecidableEq α]

private theorem card_difference_eq (A E : Finset α) :
    (A.card : ℝ) - ((A \ E).card : ℝ) = ((A ∩ E).card : ℝ) := by
  have h : (((A \ E).card : ℕ) : ℝ) + ((A ∩ E).card : ℝ) = (A.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A E
  linarith only [h]

/-- The exact counting correction is bounded by the size of the exceptional set. -/
theorem counting_difference_bounds (A E : Finset α) :
    0 ≤ (A.card : ℝ) - ((A \ E).card : ℝ) ∧
      (A.card : ℝ) - ((A \ E).card : ℝ) ≤ (E.card : ℝ) := by
  rw [card_difference_eq]
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hSubset : A ∩ E ⊆ E := Finset.inter_subset_right
  exact_mod_cast Finset.card_le_card hSubset

/-- This works for real or integer cutoffs and for any normalization tending to infinity. -/
theorem correction_tendsto_zero (A : ι → Finset α) (E : Finset α) (l : Filter ι)
    (d : ι → ℝ) (hd : Tendsto d l atTop) :
    Tendsto (fun t ↦ ((A t).card - (((A t) \ E).card : ℝ)) / d t) l (𝓝 0) := by
  have hBound := hd.const_div_atTop (E.card : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
  · filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    exact div_nonneg (counting_difference_bounds (A t) E).1 ht.le
  · filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    exact div_le_div_of_nonneg_right (counting_difference_bounds (A t) E).2 ht.le

/-- Removing the specified finite support preserves the original limiting ratio. -/
theorem remove_finite_support (A : ι → Finset α) (E : Finset α) (l : Filter ι)
    (d : ι → ℝ) (hd : Tendsto d l atTop) (r : ℝ)
    (hr : Tendsto (fun t ↦ ((A t).card : ℝ) / d t) l (𝓝 r)) :
    Tendsto (fun t ↦ (((A t) \ E).card : ℝ) / d t) l (𝓝 r) := by
  have h := hr.sub (correction_tendsto_zero A E l d hd)
  rw [sub_zero] at h
  convert h using 1
  funext t
  ring

end ManuscriptAudit.FiniteSupportCountingLimit

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.FiniteSupportCountingLimit.counting_difference_bounds,
      ``ManuscriptAudit.FiniteSupportCountingLimit.correction_tendsto_zero,
      ``ManuscriptAudit.FiniteSupportCountingLimit.remove_finite_support] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
