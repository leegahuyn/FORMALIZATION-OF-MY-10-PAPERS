import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum

/-!
# An eventually divisible sequence and its Mahler differences

Paper 8, physical p. 380, passes eventual divisibility of the input
values to the forward differences based at zero. The unit impulse
has an entirely divisible tail but every origin difference is a
unit. With a shifted base point the expected divisibility statement
is valid, and the inverse Newton identity gives its exact converse.
-/

open Filter
open scoped BigOperators Topology fwdDiff

namespace ManuscriptAudit.MahlerTail

def impulse (n : ℕ) : ℤ := if n = 0 then 1 else 0

theorem impulse_forwardDiff (j n : ℕ) :
    (Δ_[(1 : ℕ)]^[j] impulse) n = if n = 0 then (-1 : ℤ) ^ j else 0 := by
  induction j with
  | zero => simp [impulse]
  | succ j ih =>
      rw [Function.iterate_succ_apply', fwdDiff, ih, ih]
      by_cases hn : n = 0
      · subst n
        simp [pow_succ]
      · simp [hn]

/-- Every input after zero is divisible by 25, and no Mahler difference
based at zero is divisible by 25. -/
theorem paper8_eventual_divisibility_not_transferred :
    (∀ n ≥ 1, (25 : ℤ) ∣ impulse n) ∧
      ∀ j, ¬ (25 : ℤ) ∣ (Δ_[(1 : ℕ)]^[j] impulse) 0 := by
  constructor
  · intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (show 0 < n from hn)
    simp [impulse, hn0]
  · intro j
    rw [impulse_forwardDiff, if_pos rfl]
    intro hj
    have hSquare : ((-1 : ℤ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hOne : (25 : ℤ) ∣ 1 := by
      rw [← hSquare, pow_two]
      exact dvd_mul_of_dvd_left hj _
    norm_num at hOne

/-- The exact corrected criterion uses a common starting index in
the input values and all the forward differences. -/
theorem shifted_dvd_values_iff_dvd_forwardDiff (a : ℕ → ℤ) (d : ℤ) (N : ℕ) :
    (∀ k, d ∣ a (N + k)) ↔ ∀ j, d ∣ (Δ_[(1 : ℕ)]^[j] a) N := by
  constructor
  · intro h j
    rw [fwdDiff_iter_eq_sum_shift]
    apply Finset.dvd_sum
    intro k _
    simpa only [nsmul_one, zsmul_eq_mul] using
      dvd_mul_of_dvd_right (h k) ((-1 : ℤ) ^ (j - k) * (j.choose k : ℤ))
  · intro h k
    have hNewton := shift_eq_sum_fwdDiff_iter (1 : ℕ) a k N
    rw [nsmul_one] at hNewton
    rw [hNewton]
    apply Finset.dvd_sum
    intro j _
    simpa only [nsmul_eq_mul] using
      dvd_mul_of_dvd_right (h j) (k.choose j : ℤ)

/-- Tail divisibility alone cannot supply a continuous interpolation
of the entire original natural-index sequence on the p-adic integers. -/
theorem paper8_impulse_has_no_continuous_padic_extension (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : ℤ_[p] → ℤ_[p], Continuous f ∧
      ∀ n : ℕ, f (n : ℤ_[p]) = (impulse n : ℤ_[p]) := by
  rintro ⟨f, hf, hValues⟩
  have hNorm : ‖(p : ℤ_[p])‖ < 1 := by
    simpa only [PadicInt.norm_p, Padic.norm_p] using (Padic.norm_p_lt_one (p := p))
  have hPow : Tendsto (fun j : ℕ => (p : ℤ_[p]) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hNorm
  have hComp := (hf.tendsto (0 : ℤ_[p])).comp hPow
  have hEq : (fun j : ℕ => f ((p : ℤ_[p]) ^ j)) = fun _ => 0 := by
    funext j
    rw [← Nat.cast_pow, hValues]
    simp [impulse, pow_ne_zero j (Fact.out : p.Prime).ne_zero]
  change Tendsto (fun j : ℕ => f ((p : ℤ_[p]) ^ j)) atTop (𝓝 (f 0)) at hComp
  rw [hEq] at hComp
  have hZero : f 0 = 0 := tendsto_nhds_unique hComp tendsto_const_nhds
  have hOne : f 0 = 1 := by simpa [impulse] using hValues 0
  exact one_ne_zero (hOne.symm.trans hZero)

end ManuscriptAudit.MahlerTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MahlerTail.impulse_forwardDiff,
      ``ManuscriptAudit.MahlerTail.paper8_eventual_divisibility_not_transferred,
      ``ManuscriptAudit.MahlerTail.shifted_dvd_values_iff_dvd_forwardDiff,
      ``ManuscriptAudit.MahlerTail.paper8_impulse_has_no_continuous_padic_extension] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
