import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossThreeSum

/-! The lifted Jacobi weight loses exactly one prime-three factor. -/

namespace ManuscriptAudit.Paper8JacobiLiftWeight

open Paper8OddCrossThreeSum Paper8OddCrossJacobiSum Paper8ProductStationaryPhase

noncomputable section

theorem jacobiLiftWeight_eq_three_product {k : ℕ} [NeZero k] (x : (ZMod (3 * k))ˣ) :
    jacobiLiftWeight k x =
      jacobiUnitWeight (3 * k) x * (jacobiSym ((x : ZMod (3 * k)).val : ℤ) 3 : ℂ) := by
  let a := (x : ZMod (3 * k)).val
  let f := @reduceLowDigit 3 k
  let b := (f (x : ZMod (3 * k))).val
  have hb : (b : ZMod k) = (a : ZMod k) := by
    calc
      _ = f (x : ZMod (3 * k)) := ZMod.natCast_zmod_val _
      _ = f (a : ZMod (3 * k)) := by rw [show (a : ZMod (3 * k)) = x from ZMod.natCast_zmod_val _]
      _ = _ := map_natCast f a
  have hJ : jacobiSym (b : ℤ) k = jacobiSym (a : ℤ) k := by
    apply jacobiSym.mod_left'
    apply (ZMod.intCast_eq_intCast_iff' _ _ k).1
    simpa only [Int.cast_natCast] using hb
  have hA : a.Coprime (3 * k) := ZMod.val_coe_unit_coprime x
  have hC : a.Coprime 3 := Nat.Coprime.of_dvd_right (dvd_mul_right 3 k) hA
  have hG : (a : ℤ).gcd (3 : ℤ) = 1 := by
    change (a : ℤ).gcd ((3 : ℕ) : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact hC.gcd_eq_one
  have hSign : ((jacobiSym (a : ℤ) 3 : ℤ) : ℂ) ^ 2 = 1 := by
    have h : jacobiSym (a : ℤ) 3 ^ 2 = 1 := jacobiSym.sq_one hG
    exact_mod_cast h
  change (jacobiSym (b : ℤ) k : ℂ) =
    (jacobiSym (a : ℤ) (3 * k) : ℂ) * (jacobiSym (a : ℤ) 3 : ℂ)
  rw [hJ, jacobiSym.mul_right, Int.cast_mul]
  calc
    _ = (jacobiSym (a : ℤ) k : ℂ) * ((jacobiSym (a : ℤ) 3 : ℤ) : ℂ) ^ 2 := by rw [hSign, mul_one]
    _ = _ := by ring

end
end ManuscriptAudit.Paper8JacobiLiftWeight

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8JacobiLiftWeight.jacobiLiftWeight_eq_three_product
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
