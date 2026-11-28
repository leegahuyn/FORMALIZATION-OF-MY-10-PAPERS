import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Ring

/-! Quadratic reciprocity identifies the local two-adic and odd character factors. -/

namespace ManuscriptAudit.Paper8DedekindEvenCharacter

theorem jacobi_neg_two_part {h n e : ℕ} (hh : h % 2 = 1) (hn : n % 2 = 1) :
    jacobiSym (-(((2 ^ e * n : ℕ)) : ℤ)) h =
      (ZMod.χ₄ h) ^ (n / 2 + 1) * (ZMod.χ₈ h) ^ e * jacobiSym (h : ℤ) n := by
  have hhO : Odd h := Nat.odd_iff.mpr hh
  have hnO : Odd n := Nat.odd_iff.mpr hn
  have hSign : (-1 : ℤ) ^ (n / 2 * (h / 2)) = (ZMod.χ₄ h) ^ (n / 2) := by
    rw [mul_comm (n / 2) (h / 2), pow_mul, ← ZMod.χ₄_eq_neg_one_pow hh]
  rw [jacobiSym.neg _ hhO, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left,
    jacobiSym.pow_left, jacobiSym.at_two hhO, jacobiSym.quadratic_reciprocity hnO hhO,
    hSign, pow_succ]
  ring

end ManuscriptAudit.Paper8DedekindEvenCharacter

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenCharacter.jacobi_neg_two_part
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
