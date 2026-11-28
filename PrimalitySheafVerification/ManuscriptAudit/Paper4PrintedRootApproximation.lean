import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper4PrintedRealRootShift

/-! Paper 4, physical pp. 108–112: a rigorous relative error bound for
the linear approximation printed by the numerical root-shift script. -/

namespace ManuscriptAudit.Paper4PrintedRootApproximation

open Paper4PrintedRealRootShift (printedRoot mean_value_power root_shift_bound)

noncomputable section

private theorem one_sub_pow_le (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (n : ℕ) :
    1 - x ^ n ≤ (n : ℝ) * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      have hNonneg : 0 ≤ 1 - x ^ n := sub_nonneg.mpr (pow_le_one₀ hx₀ hx₁)
      calc
        1 - x ^ n * x = (1 - x) + x * (1 - x ^ n) := by ring
        _ ≤ (1 - x) + 1 * (1 - x ^ n) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hx₁ hNonneg) _
        _ ≤ _ := by linarith only [ih]

/-- Relative error of the actual \((A^p+p)^{1/p}-A\) versus the
script's linear value \(A^{-(p-1)}\). -/
theorem relative_error_bound (A : ℝ) (hA : 0 < A) (p : ℕ) (hp : 1 < p) :
    0 < 1 - A ^ (p - 1) * (printedRoot A p - A) ∧
      1 - A ^ (p - 1) * (printedRoot A p - A) ≤ ((p - 1 : ℕ) : ℝ) / A ^ p := by
  let b := printedRoot A p
  have hp₀ : 0 < p := Nat.zero_lt_of_lt hp
  obtain ⟨c, hc, ht⟩ := mean_value_power A hA p hp₀
  have hc₀ : 0 < c := hA.trans hc.1
  have hShift := root_shift_bound A hA p hp
  have hScaled : A ^ (p - 1) * (b - A) < 1 := by
    have h := (lt_div_iff₀ (pow_pos hA (p - 1))).mp hShift.2
    rwa [mul_comm] at h
  refine ⟨sub_pos.mpr hScaled, ?_⟩
  have hRatio₀ : 0 ≤ A / c := div_nonneg hA.le hc₀.le
  have hRatio₁ : A / c ≤ 1 := (div_le_one hc₀).mpr hc.1.le
  have hRatioError : 1 - A / c ≤ 1 / A ^ p := by
    calc
      1 - A / c = (c - A) / c := by rw [sub_div, div_self hc₀.ne']
      _ ≤ (b - A) / c := div_le_div_of_nonneg_right (sub_le_sub_right hc.2.le _) hc₀.le
      _ ≤ (b - A) / A := div_le_div_of_nonneg_left hShift.1.le hA hc.1.le
      _ ≤ (1 / A ^ (p - 1)) / A := div_le_div_of_nonneg_right hShift.2.le hA.le
      _ = 1 / A ^ p := by
        rw [div_div, ← pow_succ, Nat.sub_add_cancel hp₀]
  calc
    1 - A ^ (p - 1) * (b - A) = 1 - (A / c) ^ (p - 1) := by
      rw [show b - A = 1 / c ^ (p - 1) from ht, div_pow, mul_one_div]
    _ ≤ ((p - 1 : ℕ) : ℝ) * (1 - A / c) := one_sub_pow_le _ hRatio₀ hRatio₁ _
    _ ≤ _ := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hRatioError
        (Nat.cast_nonneg (p - 1 : ℕ))

end
end ManuscriptAudit.Paper4PrintedRootApproximation

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.Paper4PrintedRootApproximation.relative_error_bound
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
