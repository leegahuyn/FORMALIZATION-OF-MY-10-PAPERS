import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindKloostermanCongruence
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindFloorParity

/-! The modulo-eight phase is exactly the Legendre sign at an odd prime modulus. -/

namespace ManuscriptAudit.Paper8DedekindPrimePhase

open Finset Paper8DedekindKloostermanCongruence Paper8DedekindFloorParity

noncomputable section

theorem phase_mod_eight_floor {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1) :
    (dedekindPhaseNumerator h k : ZMod 8) =
      ((k : ZMod 8) - 1) * ((k : ZMod 8) - 2) - 4 * (dedekindFloorWeight h k : ZMod 8) := by
  let Q := dedekindFloorWeight h k
  let a : ℤ := (((h / 2 : ℕ)) : ℤ)
  let b : ℤ := (((k / 2 : ℕ)) : ℤ)
  have ha : (h : ℤ) - 1 = 2 * a := by
    have hn : h = 2 * (h / 2) + 1 := by omega
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hn
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hz
    dsimp only [a]
    linear_combination hz
  have hb : (k : ℤ) - 1 = 2 * b := by
    have hn : k = 2 * (k / 2) + 1 := by omega
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hn
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hz
    dsimp only [b]
    linear_combination hz
  have hQ : (Q : ℤ) = ∑ j : Fin k, (j.val : ℤ) * ((((h * j.val) / k : ℕ)) : ℤ) := by
    unfold Q dedekindFloorWeight
    push_cast <;> rfl
  have hDiff : dedekindPhaseNumerator h k -
      ((((k : ℤ) - 1) * ((k : ℤ) - 2)) - 4 * (Q : ℤ)) =
      8 * (a * b * (2 * (k : ℤ) - 1) - (Q : ℤ)) := by
    calc
      _ = 2 * ((h : ℤ) - 1) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1) - 8 * (Q : ℤ) := by
        unfold dedekindPhaseNumerator
        rw [← hQ]
        ring
      _ = _ := by rw [ha, hb]; ring
  have hDiv : (8 : ℤ) ∣ dedekindPhaseNumerator h k -
      ((((k : ℤ) - 1) * ((k : ℤ) - 2)) - 4 * (Q : ℤ)) :=
    ⟨_, hDiff⟩
  have hZero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).2 hDiv
  push_cast at hZero
  exact sub_eq_zero.mp hZero

theorem phase_mod_eight_legendre {p h : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hh : h % 2 = 1) (hC : h.Coprime p) :
    (dedekindPhaseNumerator h p : ZMod 8) =
      ((p : ZMod 8) - 1) * ((p : ZMod 8) - 2) - 2 +
        2 * ((legendreSym p (h : ℤ) : ℤ) : ZMod 8) := by
  let Q := dedekindFloorWeight h p
  have hp2 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp
  have hCast : (Q : ZMod 8) = ((Q % 2 : ℕ) : ZMod 8) + 2 * ((Q / 2 : ℕ) : ZMod 8) := by
    have hz := congrArg (fun n : ℕ => (n : ZMod 8)) (Nat.mod_add_div Q 2).symm
    push_cast at hz
    exact hz
  have hFour : 4 * (Q : ZMod 8) = (4 : ZMod 8) * ((Q % 2 : ℕ) : ZMod 8) := by
    conv_lhs =>
      rw [hCast, mul_add, ← mul_assoc, show (4 : ZMod 8) * 2 = 0 by decide, zero_mul, add_zero]
  have hSym : legendreSym p (h : ℤ) = (-1 : ℤ) ^ (Q % 2) :=
    (legendreSym_eq_weighted_floor hp hh hC).trans (neg_one_pow_eq_pow_mod_two _)
  have hSign : 4 * (Q : ZMod 8) = 2 - 2 * ((legendreSym p (h : ℤ) : ℤ) : ZMod 8) := by
    rw [hFour, hSym]
    have hParity : Q % 2 = 0 ∨ Q % 2 = 1 := by omega
    rcases hParity with h | h <;> rw [h] <;> decide
  rw [phase_mod_eight_floor hh hp2]
  change ((p : ZMod 8) - 1) * ((p : ZMod 8) - 2) - 4 * (Q : ZMod 8) = _
  rw [hSign]
  ring

end
end ManuscriptAudit.Paper8DedekindPrimePhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindPrimePhase.phase_mod_eight_legendre
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
