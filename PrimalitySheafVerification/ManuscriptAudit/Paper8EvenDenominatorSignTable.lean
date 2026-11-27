import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdArithmeticRows

/-! The exact signs of the four reduced-denominator classes in the literal even sector. -/

namespace ManuscriptAudit.Paper8EvenDenominatorSignTable

open Paper8OddGcdResiduePhase (modulusSign oddFactorSign)
open Paper8EvenGcdArithmeticRows (evenGcdSign sign_depends_on_mod_four)

noncomputable section

theorem sign_zero_class {D : ℕ} (hD : D % 4 = 0) (h : ℕ) :
    evenGcdSign h D = (-1 : ℂ) ^ h := by
  rw [evenGcdSign, if_neg (show D % 2 ≠ 1 by omega), if_pos hD]

theorem sign_two_class {D : ℕ} (hD : D % 4 = 2) (h : ℕ) :
    evenGcdSign h D = 1 := by
  rw [evenGcdSign, if_neg (show D % 2 ≠ 1 by omega), if_neg (show D % 4 ≠ 0 by omega)]

theorem sign_even_index_of_odd_denominator {D : ℕ} (hD : Odd D) (m : ℕ) :
    evenGcdSign (2 * m) D = (-1 : ℂ) ^ m := by
  have hMod : D % 2 = 1 := by obtain ⟨j, hj⟩ := hD; omega
  have hMul : (2 * m) * D = 2 * (m * D) := by ring
  have hDiv : (2 * (m * D) + 1) / 2 = m * D := by omega
  rw [evenGcdSign, if_pos hMod, modulusSign, hMul, hDiv, Nat.mul_comm m D, pow_mul,
    hD.neg_one_pow]

private theorem oddFactorSign_mod_four {h : ℕ} (hh : Odd h) :
    oddFactorSign h = oddFactorSign (h % 4) := by
  have hResidue : 1 ≤ h % 4 := by obtain ⟨m, hm⟩ := hh; omega
  have hExp : (h - 1) / 2 = 2 * (h / 4) + (h % 4 - 1) / 2 := by omega
  have hEven : Even (2 * (h / 4)) := ⟨h / 4, by omega⟩
  rw [oddFactorSign, oddFactorSign, hExp, pow_add, hEven.neg_one_pow, one_mul]

private theorem odd_index_residue {h : ℕ} (hh : Odd h) : h % 4 = 1 ∨ h % 4 = 3 := by
  obtain ⟨m, hm⟩ := hh
  omega

theorem sign_odd_index_of_one_class {h D : ℕ} (hh : Odd h) (hD : D % 4 = 1) :
    evenGcdSign h D = -oddFactorSign h := by
  rw [sign_depends_on_mod_four h D, hD, oddFactorSign_mod_four hh]
  rcases odd_index_residue hh with h₁ | h₃
  · rw [h₁]
    norm_num [evenGcdSign, modulusSign, oddFactorSign]
  · rw [h₃]
    norm_num [evenGcdSign, modulusSign, oddFactorSign]

theorem sign_odd_index_of_three_class {h D : ℕ} (hh : Odd h) (hD : D % 4 = 3) :
    evenGcdSign h D = oddFactorSign h := by
  rw [sign_depends_on_mod_four h D, hD, oddFactorSign_mod_four hh]
  rcases odd_index_residue hh with h₁ | h₃
  · rw [h₁]
    norm_num [evenGcdSign, modulusSign, oddFactorSign]
  · rw [h₃]
    norm_num [evenGcdSign, modulusSign, oddFactorSign]

end
end ManuscriptAudit.Paper8EvenDenominatorSignTable

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenDenominatorSignTable.sign_zero_class,
      ``ManuscriptAudit.Paper8EvenDenominatorSignTable.sign_two_class,
      ``ManuscriptAudit.Paper8EvenDenominatorSignTable.sign_even_index_of_odd_denominator,
      ``ManuscriptAudit.Paper8EvenDenominatorSignTable.sign_odd_index_of_one_class,
      ``ManuscriptAudit.Paper8EvenDenominatorSignTable.sign_odd_index_of_three_class] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
