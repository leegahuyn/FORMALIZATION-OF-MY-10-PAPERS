import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Arithmetic separation of the printed Rademacher and Cauchy values

The input is the literal decimal mantissas on physical page 349.
Allowing a full last displayed place of error in each real part
still leaves the two complex values farther apart than the displayed
Rademacher tolerance.
-/

namespace ManuscriptAudit.Paper8AppendixComparison

noncomputable section

private theorem norm_gap_of_rounded_real_parts {r c : ℂ} {r₀ c₀ u B : ℝ}
    (hr : |r.re - r₀| ≤ u) (hc : |c.re - c₀| ≤ u)
    (hGap : B < r₀ - c₀ - 2 * u) : B < ‖r - c‖ := by
  have hR := (abs_le.mp hr).1
  have hC := (abs_le.mp hc).2
  have hDiff : B < (r - c).re := by
    rw [Complex.sub_re]
    linarith
  exact (hDiff.trans_le (le_abs_self _)).trans_le (Complex.abs_re_le_norm _)

theorem paper8_n10_printed_rad_cauchy_gap {r c : ℂ}
    (hr : |r.re - (5658773842583 : ℝ) * 10 ^ (4 : ℕ)| ≤ 10 ^ (4 : ℕ))
    (hc : |c.re - (3504363460048 : ℝ) * 10 ^ (4 : ℕ)| ≤ 10 ^ (4 : ℕ)) :
    (1295 : ℝ) < ‖r - c‖ :=
  norm_gap_of_rounded_real_parts hr hc (by norm_num)

theorem paper8_n20_printed_rad_cauchy_gap {r c : ℂ}
    (hr : |r.re - (6699209775749 : ℝ) * 10 ^ (11 : ℕ)| ≤ 10 ^ (11 : ℕ))
    (hc : |c.re - (6699083909299 : ℝ) * 10 ^ (11 : ℕ)| ≤ 10 ^ (11 : ℕ)) :
    (1560 : ℝ) < ‖r - c‖ :=
  norm_gap_of_rounded_real_parts hr hc (by norm_num)

theorem paper8_n30_printed_rad_cauchy_gap {r c : ℂ}
    (hr : |r.re - (1850473230691 : ℝ) * 10 ^ (17 : ℕ)| ≤ 10 ^ (17 : ℕ))
    (hc : |c.re - (1850473222306 : ℝ) * 10 ^ (17 : ℕ)| ≤ 10 ^ (17 : ℕ)) :
    (1743 : ℝ) < ‖r - c‖ :=
  norm_gap_of_rounded_real_parts hr hc (by norm_num)

end
end ManuscriptAudit.Paper8AppendixComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8AppendixComparison.paper8_n10_printed_rad_cauchy_gap,
      ``ManuscriptAudit.Paper8AppendixComparison.paper8_n20_printed_rad_cauchy_gap,
      ``ManuscriptAudit.Paper8AppendixComparison.paper8_n30_printed_rad_cauchy_gap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
