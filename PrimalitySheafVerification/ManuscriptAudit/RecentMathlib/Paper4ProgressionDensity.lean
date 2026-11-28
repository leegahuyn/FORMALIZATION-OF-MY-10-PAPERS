import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LSeries.WeakPNT
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportCountingLimit

/-! Paper 4, physical pp. 139–140: the exact prime number theorem in reduced
arithmetic progressions survives removal of any specified finite prime support. -/

namespace ManuscriptAudit.Paper4ProgressionDensity

open Filter Topology Finset

noncomputable section

def progressionCutoff (a q : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter (fun p ↦ p.Prime ∧ p ≡ a [MOD q])

def primeCutoff (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime

private theorem ratioNormalizer_tendsto :
    Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have hScale : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] (0 : ℝ)) := by
    change Tendsto (fun x : ℝ ↦ Real.log x / x) atTop
      (𝓝 (0 : ℝ) ⊓ 𝓟 (Set.Ioi (0 : ℝ)))
    apply tendsto_inf.mpr
    constructor
    · simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    · rw [Filter.tendsto_principal]
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (Real.log_pos hx) (zero_lt_one.trans hx)
  exact (tendsto_inv_nhdsGT_zero.comp hScale).congr (fun x ↦ inv_div _ _)

/-- The actual normalized prime count in a reduced progression, after removal
of any fixed finite support. -/
theorem normalized_count_after_exceptions {a q : ℕ} [NeZero q] (h : a.Coprime q)
    (E : Finset ℕ) :
    Tendsto (fun x : ℝ ↦ (((progressionCutoff a q x) \ E).card : ℝ) / (x / Real.log x))
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hProgression :
      Tendsto (fun x : ℝ ↦ ((progressionCutoff a q x).card : ℝ) / (x / Real.log x))
        atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa only [progressionCutoff, div_div_eq_mul_div] using
      Nat.tendsto_card_prime_modEq_mul_log_div_atTop h
  exact FiniteSupportCountingLimit.remove_finite_support
    (progressionCutoff a q) E atTop _ ratioNormalizer_tendsto _ hProgression

/-- The actual proportion among all primes tends to the inverse totient,
and gives the same answer after deleting any finite exceptional support. -/
theorem relative_prime_density_after_exceptions {a q : ℕ} [NeZero q] (h : a.Coprime q)
    (E : Finset ℕ) :
    Tendsto (fun x : ℝ ↦ (((progressionCutoff a q x) \ E).card : ℝ) / (primeCutoff x).card)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hAll : Tendsto (fun x : ℝ ↦ ((primeCutoff x).card : ℝ) / (x / Real.log x))
      atTop (𝓝 (1 : ℝ)) := by
    simpa [progressionCutoff, primeCutoff, Nat.ModEq] using
      (normalized_count_after_exceptions (q := 1) (a := 1) (Nat.coprime_one_left 1) ∅)
  have hRatio := (normalized_count_after_exceptions h E).div hAll one_ne_zero
  rw [div_one] at hRatio
  apply hRatio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hd : x / Real.log x ≠ 0 :=
    div_ne_zero (zero_lt_one.trans hx).ne' (Real.log_pos hx).ne'
  exact div_div_div_cancel_right₀ hd _ _

end
end ManuscriptAudit.Paper4ProgressionDensity

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ProgressionDensity.normalized_count_after_exceptions,
      ``ManuscriptAudit.Paper4ProgressionDensity.relative_prime_density_after_exceptions] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
