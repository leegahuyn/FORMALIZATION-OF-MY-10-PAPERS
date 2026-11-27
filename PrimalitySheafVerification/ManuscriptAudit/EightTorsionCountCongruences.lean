import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring

/-! The group orders at quadratic and quartic extension degrees have distinct two-power divisibilities. -/

namespace ManuscriptAudit.EightTorsionCountCongruences

theorem quadratic_dvd_of_seven (p : ℕ) (hp : p % 8 = 7) :
    64 ∣ (p + 1) ^ 2 := by
  have he : p + 1 = 8 * (p / 8 + 1) := by omega
  refine ⟨(p / 8 + 1) ^ 2, ?_⟩
  rw [he]
  ring

theorem quadratic_not_dvd_of_three (p : ℕ) (hp : p % 8 = 3) :
    ¬ 64 ∣ (p + 1) ^ 2 := by
  have he : p + 1 = 8 * (p / 8) + 4 := by omega
  have hs : (p + 1) ^ 2 = 64 * ((p / 8) ^ 2 + p / 8) + 16 := by rw [he]; ring
  rw [Nat.dvd_iff_mod_eq_zero, hs]
  omega

theorem quartic_dvd_of_one (p : ℕ) (hp : p % 8 = 1) :
    256 ∣ (p ^ 2 - 1) ^ 2 := by
  let k := p / 8
  have hp' : p = 8 * k + 1 := by dsimp [k]; omega
  have hs : p ^ 2 = 16 * (4 * k ^ 2 + k) + 1 := by rw [hp']; ring
  have hdiff : p ^ 2 - 1 = 16 * (4 * k ^ 2 + k) := by rw [hs, Nat.add_sub_cancel]
  refine ⟨(4 * k ^ 2 + k) ^ 2, ?_⟩
  rw [hdiff]
  ring

theorem quartic_not_dvd_of_five (p : ℕ) (hp : p % 8 = 5) :
    ¬ 256 ∣ (p ^ 2 - 1) ^ 2 := by
  let k := p / 8
  let s := 4 * k ^ 2 + 5 * k + 1
  have hp' : p = 8 * k + 5 := by dsimp [k]; omega
  have hs : p ^ 2 = (16 * s + 8) + 1 := by rw [hp']; dsimp only [s]; ring
  have hdiff : p ^ 2 - 1 = 16 * s + 8 := by rw [hs, Nat.add_sub_cancel]
  have hSq : (p ^ 2 - 1) ^ 2 = 256 * (s ^ 2 + s) + 64 := by rw [hdiff]; ring
  rw [Nat.dvd_iff_mod_eq_zero, hSq]
  omega

end ManuscriptAudit.EightTorsionCountCongruences

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.EightTorsionCountCongruences.quadratic_dvd_of_seven,
      ``ManuscriptAudit.EightTorsionCountCongruences.quadratic_not_dvd_of_three,
      ``ManuscriptAudit.EightTorsionCountCongruences.quartic_dvd_of_one,
      ``ManuscriptAudit.EightTorsionCountCongruences.quartic_not_dvd_of_five] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
