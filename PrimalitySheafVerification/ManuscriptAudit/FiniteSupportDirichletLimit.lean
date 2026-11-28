import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

/-! A fixed finite set of positive integers contributes zero to the natural
Dirichlet normalization at s = 1 from above. -/

namespace ManuscriptAudit.FiniteSupportDirichletLimit

open Filter Topology
open scoped BigOperators

noncomputable section

def normalizer (s : ℝ) : ℝ := Real.log ((s - 1)⁻¹)

theorem normalizer_tendsto : Tendsto normalizer (𝓝[>] (1 : ℝ)) atTop := by
  have hShift : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    change Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ))
      (𝓝 (0 : ℝ) ⊓ 𝓟 (Set.Ioi (0 : ℝ)))
    apply tendsto_inf.mpr
    constructor
    · have h : Continuous (fun s : ℝ ↦ s - 1) := continuous_id.sub continuous_const
      simpa using (h.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · rw [Filter.tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr hs
  have hInv : Tendsto (fun s : ℝ ↦ (s - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hShift
  exact Real.tendsto_log_atTop.comp hInv

def finiteWeight (E : Finset ℕ) (s : ℝ) : ℝ :=
  ∑ p ∈ E, (p : ℝ) ^ (-s)

theorem finiteWeight_bounds (E : Finset ℕ) (hE : ∀ p ∈ E, 0 < p)
    (s : ℝ) (hs : 0 ≤ s) : 0 ≤ finiteWeight E s ∧ finiteWeight E s ≤ E.card := by
  constructor
  · exact Finset.sum_nonneg (fun p _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
  · calc
      finiteWeight E s ≤ ∑ p ∈ E, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : 1 ≤ p := hE p hp
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast hp') (neg_nonpos.mpr hs)
      _ = (E.card : ℝ) := by simp

/-- In particular, every finite exceptional prime support has Dirichlet density zero. -/
theorem normalized_finiteWeight_tendsto_zero (E : Finset ℕ) (hE : ∀ p ∈ E, 0 < p) :
    Tendsto (fun s ↦ finiteWeight E s / normalizer s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hBound := normalizer_tendsto.const_div_atTop (E.card : ℝ)
  have hNear : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 1 < s := self_mem_nhdsWithin
  have hDenom := normalizer_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
  · filter_upwards [hNear, hDenom] with s hs hd
    exact div_nonneg (finiteWeight_bounds E hE s (zero_le_one.trans hs.le)).1 hd.le
  · filter_upwards [hNear, hDenom] with s hs hd
    exact div_le_div_of_nonneg_right (finiteWeight_bounds E hE s (zero_le_one.trans hs.le)).2 hd.le

end
end ManuscriptAudit.FiniteSupportDirichletLimit

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.FiniteSupportDirichletLimit.normalizer_tendsto,
      ``ManuscriptAudit.FiniteSupportDirichletLimit.normalized_finiteWeight_tendsto_zero] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
