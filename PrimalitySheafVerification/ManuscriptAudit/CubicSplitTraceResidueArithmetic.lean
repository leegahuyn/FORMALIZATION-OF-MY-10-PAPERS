import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic

/-! Recovering an odd trace modulo four from the cubic-extension trace modulo eight. -/

namespace ManuscriptAudit.CubicSplitTraceResidueArithmetic

private def lowerFour : ZMod 8 →+* ZMod 4 :=
  ZMod.castHom (by decide : (4 : ℕ) ∣ 8) (ZMod 4)

private def lowerTwo : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by decide : (2 : ℕ) ∣ 8) (ZMod 2)

private theorem rule :
    ∀ q t : ZMod 8, lowerFour q = 1 → lowerTwo t = 1 →
      (t ^ 3 - 3 * q * t = q ^ 3 + 1 → lowerFour t = 3) ∧
      (t ^ 3 - 3 * q * t = q ^ 3 - 3 → lowerFour t = 1) := by decide

theorem trace_mod_four_of_third_trace (q : ℕ) (t : ℤ)
    (hq : (q : ZMod 4) = 1) (ht : (t : ZMod 2) = 1) :
    (((t ^ 3 - 3 * (q : ℤ) * t : ℤ) : ZMod 8) = (q : ZMod 8) ^ 3 + 1 →
      (t : ZMod 4) = 3) ∧
    (((t ^ 3 - 3 * (q : ℤ) * t : ℤ) : ZMod 8) = (q : ZMod 8) ^ 3 - 3 →
      (t : ZMod 4) = 1) := by
  have hq₈ : lowerFour (q : ZMod 8) = 1 := by simpa only [map_natCast] using hq
  have ht₈ : lowerTwo (t : ZMod 8) = 1 := by simpa only [map_intCast] using ht
  simpa only [map_intCast, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat] using rule (q : ZMod 8) (t : ZMod 8) hq₈ ht₈

end ManuscriptAudit.CubicSplitTraceResidueArithmetic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitTraceResidueArithmetic.trace_mod_four_of_third_trace
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
