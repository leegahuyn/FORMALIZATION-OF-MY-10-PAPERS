import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Data.Nat.Factorization.Basic
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

private theorem all_primes_normalized (F : Finset ℕ) :
    Tendsto (fun x : ℝ ↦ (((primeCutoff x) \ F).card : ℝ) / (x / Real.log x))
      atTop (𝓝 (1 : ℝ)) := by
  have hSame (x : ℝ) : progressionCutoff 1 1 x = primeCutoff x := by
    ext p
    have hMod : p ≡ 1 [MOD 1] := by
      change p % 1 = 1 % 1
      simp only [Nat.mod_one]
    simp [progressionCutoff, primeCutoff, hMod]
  simpa only [hSame, Nat.totient_one, Nat.cast_one, inv_one] using
    (normalized_count_after_exceptions (q := 1) (a := 1) (Nat.coprime_one_left 1) F)

/-- The proportion among primes has the same limit after fixed finite
deletions from both the progression count and the total count. -/
theorem relative_prime_density_after_finite_changes {a q : ℕ} [NeZero q]
    (h : a.Coprime q) (E F : Finset ℕ) :
    Tendsto (fun x : ℝ ↦ (((progressionCutoff a q x) \ E).card : ℝ) /
      (((primeCutoff x) \ F).card : ℝ)) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hAll := all_primes_normalized F
  have hRatio := (normalized_count_after_exceptions h E).div hAll one_ne_zero
  rw [div_one] at hRatio
  apply hRatio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hd : x / Real.log x ≠ 0 :=
    div_ne_zero (zero_lt_one.trans hx).ne' (Real.log_pos hx).ne'
  exact div_div_div_cancel_right₀ hd _ _

/-- The actual fraction among all primes after deleting the specified exceptions. -/
theorem relative_prime_density_after_exceptions {a q : ℕ} [NeZero q] (h : a.Coprime q)
    (E : Finset ℕ) :
    Tendsto (fun x : ℝ ↦ (((progressionCutoff a q x) \ E).card : ℝ) / (primeCutoff x).card)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  simpa using relative_prime_density_after_finite_changes h E ∅


/-- Actual primes in the cutoff that divide either specified integer. -/
def exceptionalPrimeCutoff (g d : ℕ) (x : ℝ) : Finset ℕ :=
  (primeCutoff x).filter (fun p ↦ p ∣ g ∨ p ∣ d)

/-- Actual primes in the prescribed progression that divide neither integer. -/
def goodPrimeCutoff (a q g d : ℕ) (x : ℝ) : Finset ℕ :=
  (progressionCutoff a q x).filter (fun p ↦ ¬ p ∣ g ∧ ¬ p ∣ d)

private theorem exceptional_subset {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0) (x : ℝ) :
    exceptionalPrimeCutoff g d x ⊆ g.primeFactors ∪ d.primeFactors := by
  intro p hp
  obtain ⟨hp, hDiv⟩ := Finset.mem_filter.mp hp
  have hPrime := (Finset.mem_filter.mp hp).2
  exact Finset.mem_union.mpr (hDiv.imp (fun h ↦ hPrime.mem_primeFactors h hg)
    (fun h ↦ hPrime.mem_primeFactors h hd))

private theorem exceptional_over_divergent {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0)
    (D : ℝ → ℝ) (hD : Tendsto D atTop atTop) :
    Tendsto (fun x : ℝ ↦ ((exceptionalPrimeCutoff g d x).card : ℝ) / D x) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hD.const_div_atTop ((g.primeFactors ∪ d.primeFactors).card : ℝ))
  · filter_upwards [hD.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact div_nonneg (Nat.cast_nonneg _) hx.le
  · filter_upwards [hD.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    apply div_le_div_of_nonneg_right _ hx.le
    exact_mod_cast Finset.card_le_card (exceptional_subset hg hd x)

/-- The literal exceptional primes have natural density zero among all integers. -/
theorem exceptional_natural_density {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0) :
    Tendsto (fun x : ℝ ↦ ((exceptionalPrimeCutoff g d x).card : ℝ) / x) atTop (𝓝 0) :=
  exceptional_over_divergent hg hd id tendsto_id

/-- The same literal set has natural density zero relative to all primes. -/
theorem exceptional_relative_prime_density {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0) :
    Tendsto (fun x : ℝ ↦ ((exceptionalPrimeCutoff g d x).card : ℝ) /
      (primeCutoff x).card) atTop (𝓝 0) := by
  have hRatio := (exceptional_over_divergent hg hd _ ratioNormalizer_tendsto).div
    (all_primes_normalized ∅) one_ne_zero
  rw [zero_div] at hRatio
  apply hRatio.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hScale : x / Real.log x ≠ 0 :=
    div_ne_zero (zero_lt_one.trans hx).ne' (Real.log_pos hx).ne'
  change (((exceptionalPrimeCutoff g d x).card : ℝ) / (x / Real.log x)) /
    ((((primeCutoff x) \ ∅).card : ℝ) / (x / Real.log x)) = _
  rw [Finset.sdiff_empty, div_div_div_cancel_right₀ hScale]

/-- Exact progression density after imposing the gcd and discriminant prime conditions. -/
theorem good_progression_prime_density {a q g d : ℕ} [NeZero q] (ha : a.Coprime q)
    (hg : g ≠ 0) (hd : d ≠ 0) :
    Tendsto (fun x : ℝ ↦ ((goodPrimeCutoff a q g d x).card : ℝ) /
      (primeCutoff x).card) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hCutoff (x : ℝ) :
      goodPrimeCutoff a q g d x = progressionCutoff a q x \ (g.primeFactors ∪ d.primeFactors) := by
    ext p
    by_cases hp : p.Prime
    · simp [goodPrimeCutoff, Nat.mem_primeFactors, hp, hg, hd, not_or]
    · simp [goodPrimeCutoff, progressionCutoff, hp]
  simpa only [hCutoff] using
    relative_prime_density_after_exceptions ha (g.primeFactors ∪ d.primeFactors)

end
end ManuscriptAudit.Paper4ProgressionDensity

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ProgressionDensity.normalized_count_after_exceptions,
      ``ManuscriptAudit.Paper4ProgressionDensity.relative_prime_density_after_finite_changes,
      ``ManuscriptAudit.Paper4ProgressionDensity.relative_prime_density_after_exceptions,
      ``ManuscriptAudit.Paper4ProgressionDensity.exceptional_natural_density,
      ``ManuscriptAudit.Paper4ProgressionDensity.exceptional_relative_prime_density,
      ``ManuscriptAudit.Paper4ProgressionDensity.good_progression_prime_density] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
