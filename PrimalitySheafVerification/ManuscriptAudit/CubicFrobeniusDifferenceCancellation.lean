import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! Arithmetic cancellation predicted by the actual rational ordinates of the centered cubic. -/

namespace ManuscriptAudit.CubicFrobeniusDifferenceCancellation

open FiniteFieldPointCount
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K]

/-- The local cancellation count: one at zero ordinate, two at a nonzero nonsquare,
and zero at a nonzero square. -/
def cancellation (k : ℕ) (A x : K) : ℕ := by
  classical
  exact if x ^ 3 + A = 0 then 1 else if (x ^ 3 + A) ^ k = -1 then 2 else 0

open scoped Classical in
theorem cast_cancellation {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (h₂ : (2 : K) ≠ 0) (hchar : ringChar K ≠ 2) (A x : K) :
    (cancellation K k A x : ℤ) = 1 - quadraticChar K (x ^ 3 + A) := by
  classical
  let s := x ^ 3 + A
  change ((if s = 0 then 1 else if s ^ k = -1 then 2 else 0 : ℕ) : ℤ) =
    1 - quadraticChar K s
  have hk : Fintype.card K / 2 = k := by omega
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hchar s
  rw [hk] at hpow
  by_cases hs : s = 0
  · simp [hs, quadraticChar_zero]
  · rcases quadraticChar_dichotomy hs with h | h
    · have hs' : s ^ k = 1 := by simpa only [h, Int.cast_one] using hpow.symm
      have hne : (1 : K) ≠ -1 := by
        intro he
        apply h₂
        linear_combination he
      simp [hs, hs', hne, h]
    · have hs' : s ^ k = -1 := by simpa only [h, Int.cast_neg, Int.cast_one] using hpow.symm
      norm_num [hs, hs', h]

/-- Subtracting the arithmetic cancellation from the expected numerator degree gives
exactly the actual projective point count. -/
theorem count_add_cancellation {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2)
    {A : K} (hA : A ≠ 0) :
    Nat.card (shortCubic (0 : K) A).toProjective.Point + ∑ x : K, cancellation K k A x =
      2 * Fintype.card K + 1 := by
  classical
  have hCount : (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) =
      (Fintype.card K : ℤ) + 1 + ∑ x : K, quadraticChar K (x ^ 3 + A) := by
    simpa only [zero_mul, sub_zero] using
      shortCubic_projective_count_int hchar
        (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have hCancel : ((∑ x : K, cancellation K k A x : ℕ) : ℤ) =
      (Fintype.card K : ℤ) - ∑ x : K, quadraticChar K (x ^ 3 + A) := by
    simp_rw [Nat.cast_sum, cast_cancellation K hq h₂ hchar]
    rw [Finset.sum_sub_distrib]
    simp
  have he : (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) +
      ((∑ x : K, cancellation K k A x : ℕ) : ℤ) = 2 * (Fintype.card K : ℤ) + 1 := by
    rw [hCount, hCancel]
    ring
  exact_mod_cast he

end

end ManuscriptAudit.CubicFrobeniusDifferenceCancellation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusDifferenceCancellation.cast_cancellation,
      ``ManuscriptAudit.CubicFrobeniusDifferenceCancellation.count_add_cancellation] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
