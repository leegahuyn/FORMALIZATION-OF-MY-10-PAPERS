import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# A finite-field polynomial sum for the genuine elliptic point count

For a finite field of size q, evaluation summed over the field extracts
the negative coefficient of degree q−1 from any polynomial of degree
less than 2(q−1). This is the degree bound in the Paper 5 cubic calculation.
-/

namespace ManuscriptAudit.FiniteFieldPowerSums

open scoped BigOperators
open Finset

private theorem sum_field_powers_eq_sum_unit_powers (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (n : ℕ) (hn : n ≠ 0) :
    (∑ x : K, x ^ n) = ∑ x : Kˣ, (x ^ n : K) := by
  classical
  let e : Kˣ ↪ K := ⟨fun u => u, Units.val_injective⟩
  have he : univ.map e = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, e] using! isUnit_iff_ne_zero
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hn, add_zero, ← he]
  simp [e]

/-- A power sum below twice the first positive multiple of q−1. -/
theorem finite_field_power_sum_low_degrees (K : Type*) [Field K] [Fintype K]
    (hq : 1 < Fintype.card K) (n : ℕ) (hn : n < (Fintype.card K - 1) * 2) :
    (∑ x : K, x ^ n) = if n = Fintype.card K - 1 then -1 else 0 := by
  classical
  by_cases hn0 : n = 0
  · have hq0 : 0 ≠ Fintype.card K - 1 := by omega
    simp [hn0, hq0, FiniteField.cast_card_eq_zero]
  · rw [sum_field_powers_eq_sum_unit_powers K n hn0, FiniteField.sum_pow_units K]
    have hdiv : Fintype.card K - 1 ∣ n ↔ n = Fintype.card K - 1 := by
      constructor
      · rintro ⟨d, hd⟩
        have hd0 : d ≠ 0 := by
          intro hz
          exact hn0 (by simpa [hz] using hd)
        by_cases hd1 : d = 1
        · simpa [hd1] using hd
        · have hd2 : 2 ≤ d := by omega
          exact False.elim ((not_le_of_gt hn) (hd ▸ Nat.mul_le_mul_left _ hd2))
      · rintro rfl
        exact dvd_refl _
    by_cases heq : n = Fintype.card K - 1
    · simp only [if_pos (hdiv.mpr heq), if_pos heq]
    · simp only [if_neg (mt hdiv.mp heq), if_neg heq]

/-- The sum of a genuine polynomial over the actual finite field. -/
theorem finite_field_sum_eval_eq_neg_coeff (K : Type*) [Field K] [Fintype K]
    (hq : 1 < Fintype.card K) (f : Polynomial K)
    (hf : f.natDegree < (Fintype.card K - 1) * 2) :
    (∑ x : K, f.eval x) = -f.coeff (Fintype.card K - 1) := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ = ∑ n ∈ f.support, f.coeff n * (if n = Fintype.card K - 1 then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [finite_field_power_sum_low_degrees K hq n
        ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)).trans_lt hf)]
    _ = _ := by
      rw [Finset.sum_eq_single (Fintype.card K - 1)]
      · simp
      · intro n _ hn
        simp [hn]
      · intro hn
        simp [(Polynomial.notMem_support_iff.mp hn)]

end ManuscriptAudit.FiniteFieldPowerSums

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteFieldPowerSums.finite_field_power_sum_low_degrees,
      ``ManuscriptAudit.FiniteFieldPowerSums.finite_field_sum_eval_eq_neg_coeff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
