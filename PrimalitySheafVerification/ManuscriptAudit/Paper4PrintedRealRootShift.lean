import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-! The real root shift tabulated in Paper 4 has a uniform, explicit
strict bound for every positive input A and every exponent p greater than one. -/

namespace ManuscriptAudit.Paper4PrintedRealRootShift

noncomputable section

def printedRoot (A : ℝ) (p : ℕ) : ℝ :=
  (A ^ p + (p : ℝ)) ^ ((p : ℝ)⁻¹)

private theorem root_pow (A : ℝ) (hA : 0 ≤ A) (p : ℕ) (hp : 0 < p) :
    printedRoot A p ^ p = A ^ p + (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hz : 0 ≤ A ^ p + (p : ℝ) := add_nonneg (pow_nonneg hA _) hpR.le
  rw [printedRoot, ← Real.rpow_mul_natCast hz, inv_mul_cancel₀ hpR.ne', Real.rpow_one]

theorem root_gt (A : ℝ) (hA : 0 ≤ A) (p : ℕ) (hp : 0 < p) :
    A < printedRoot A p := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hB : (A ^ p) ^ ((p : ℝ)⁻¹) = A := by
    rw [← Real.rpow_natCast_mul hA, mul_inv_cancel₀ hpR.ne', Real.rpow_one]
  calc
    A = (A ^ p) ^ ((p : ℝ)⁻¹) := hB.symm
    _ < printedRoot A p :=
      Real.rpow_lt_rpow (pow_nonneg hA _) (lt_add_of_pos_right _ hpR) (inv_pos.mpr hpR)

/-- The exact shift is the inverse power at an intermediate point. -/
theorem mean_value_power (A : ℝ) (hA : 0 < A) (p : ℕ) (hp : 0 < p) :
    ∃ c ∈ Set.Ioo A (printedRoot A p),
      printedRoot A p - A = 1 / c ^ (p - 1) := by
  let b := printedRoot A p
  have hLess : A < b := root_gt A hA.le p hp
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hb : b ^ p = A ^ p + (p : ℝ) := root_pow A hA.le p hp
  have hC : Continuous (fun x : ℝ ↦ x ^ p) := continuous_id.pow p
  have hD : Differentiable ℝ (fun x : ℝ ↦ x ^ p) := differentiable_id.pow p
  obtain ⟨c, hc, hm⟩ := exists_deriv_eq_slope (fun x : ℝ ↦ x ^ p) hLess
    hC.continuousOn hD.differentiableOn
  have hnum : b ^ p - A ^ p = (p : ℝ) := by rw [hb] <;> ring
  have hSlope : (p : ℝ) * c ^ (p - 1) = (p : ℝ) / (b - A) := by
    simpa only [deriv_pow_field, hnum] using hm
  have hPos : 0 < c := hA.trans hc.1
  have ht : 0 < b - A := sub_pos.mpr hLess
  have hProd : (p : ℝ) * (c ^ (p - 1) * (b - A)) = (p : ℝ) * 1 := by
    rw [← mul_assoc, (eq_div_iff ht.ne').mp hSlope, mul_one]
  have hScalar := mul_left_cancel₀ hpR.ne' hProd
  refine ⟨c, hc, (eq_div_iff (pow_pos hPos _).ne').mpr ?_⟩
  simpa only [mul_comm] using hScalar

/-- In the printed range the exact real root difference is positive and
strictly smaller than 1/A^(p−1). -/
theorem root_shift_bound (A : ℝ) (hA : 0 < A) (p : ℕ) (hp : 1 < p) :
    0 < printedRoot A p - A ∧ printedRoot A p - A < 1 / A ^ (p - 1) := by
  have hp₀ : 0 < p := Nat.zero_lt_of_lt hp
  obtain ⟨c, hc, ht⟩ := mean_value_power A hA p hp₀
  have he : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hp
  have hPow : A ^ (p - 1) < c ^ (p - 1) := by
    simpa only [Real.rpow_natCast] using Real.rpow_lt_rpow hA.le hc.1 he
  refine ⟨sub_pos.mpr (root_gt A hA.le p hp₀), ?_⟩
  rw [ht]
  exact one_div_lt_one_div_of_lt (pow_pos hA _) hPow

end
end ManuscriptAudit.Paper4PrintedRealRootShift

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4PrintedRealRootShift.root_gt,
      ``ManuscriptAudit.Paper4PrintedRealRootShift.mean_value_power,
      ``ManuscriptAudit.Paper4PrintedRealRootShift.root_shift_bound] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
