import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourCoefficientDecay

/-! The p. 335 Laurent tail after the common m = 0 term. -/

namespace ManuscriptAudit.Paper8ContourGammaRemainder

open Paper8ContourGammaSeries (a term majorant coefficient_pos majorant_summable absolute_summable
  norm_term_le_majorant)
open Paper8ContourCoefficientDecay (coefficient_succ_le_decay)
open Paper8ContourSignedDominance (decay decay_nonneg)

noncomputable section

def remainder (k : ℕ) (s : ℂ) : ℂ := ∑' m : ℕ, term k (m + 1) s

def bound (r : ℝ) : ℝ := ∑' m : ℕ, majorant 1 r (m + 1)

theorem bound_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ bound r :=
  tsum_nonneg fun m => div_nonneg (coefficient_pos (by decide : 0 < (1 : ℕ)) (m + 1)).le
    (pow_nonneg hr.le _)

theorem a_eq_first_add_remainder {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : s ≠ 0) :
    a k s = term k 0 s + remainder k s :=
  (absolute_summable hk hs).of_norm.tsum_eq_zero_add

theorem remainder_norm_le {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r)
    {s : ℂ} (hs : r ≤ ‖s‖) :
    ‖remainder k s‖ ≤ decay k * bound r := by
  have hMajorant₁ : Summable (fun m : ℕ => majorant 1 r (m + 1)) :=
    (summable_nat_add_iff 1).2 (majorant_summable (by decide : 0 < (1 : ℕ)) hr)
  have hMajorant : Summable (fun m : ℕ => decay k * majorant 1 r (m + 1)) :=
    hMajorant₁.mul_left (decay k)
  have hTerm (m : ℕ) : ‖term k (m + 1) s‖ ≤ decay k * majorant 1 r (m + 1) := by
    calc
      _ ≤ majorant k r (m + 1) := norm_term_le_majorant hk hr hs (m + 1)
      _ ≤ _ := by
        unfold majorant
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (coefficient_succ_le_decay hk m) (pow_nonneg hr.le _)
  have hAbs : Summable (fun m : ℕ => ‖term k (m + 1) s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTerm hMajorant
  calc
    _ ≤ ∑' m : ℕ, ‖term k (m + 1) s‖ := norm_tsum_le_tsum_norm hAbs
    _ ≤ ∑' m : ℕ, decay k * majorant 1 r (m + 1) := hAbs.tsum_le_tsum hTerm hMajorant
    _ = _ := tsum_mul_left

end
end ManuscriptAudit.Paper8ContourGammaRemainder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourGammaRemainder.bound_nonneg,
      ``ManuscriptAudit.Paper8ContourGammaRemainder.a_eq_first_add_remainder,
      ``ManuscriptAudit.Paper8ContourGammaRemainder.remainder_norm_le] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
