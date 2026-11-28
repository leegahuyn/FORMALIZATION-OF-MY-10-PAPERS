import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossJacobiSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimeQuadraticPhase

/-! The native Jacobi weight factors by CRT and through prime reduction at prime powers. -/

namespace ManuscriptAudit.Paper8JacobiWeightCRT

open Paper8OddCrossJacobiSum Paper8ZModAdditiveCRT Paper8PrimeQuadraticPhase

noncomputable section

theorem jacobiUnitWeight_chineseRemainder {n m : ℕ} [NeZero n] [NeZero m]
    (h : n.Coprime m) (x : (ZMod (n * m))ˣ) :
    jacobiUnitWeight (n * m) x =
      jacobiUnitWeight n (unitsChineseRemainder h x).1 *
      jacobiUnitWeight m (unitsChineseRemainder h x).2 := by
  let a := (x : ZMod (n * m)).val
  let y := (unitsChineseRemainder h x).1
  let z := (unitsChineseRemainder h x).2
  have hCast : ZMod.chineseRemainder h (x : ZMod (n * m)) = (↑y, ↑z) := rfl
  have hNM : ZMod.chineseRemainder h (x : ZMod (n * m)) = ((a : ZMod n), (a : ZMod m)) := by
    have hVal : (a : ZMod (n * m)) = x := ZMod.natCast_zmod_val _
    rw [← hVal, map_natCast]
    rfl
  have hN : ((y : ZMod n).val : ZMod n) = (a : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
    exact congrArg Prod.fst (hCast.symm.trans hNM)
  have hM : ((z : ZMod m).val : ZMod m) = (a : ZMod m) := by
    rw [ZMod.natCast_zmod_val]
    exact congrArg Prod.snd (hCast.symm.trans hNM)
  have hJ {b c : ℕ} (d : ℕ) (hB : (b : ZMod d) = c) : jacobiSym (b : ℤ) d = jacobiSym (c : ℤ) d := by
    apply jacobiSym.mod_left'
    apply (ZMod.intCast_eq_intCast_iff' _ _ d).1
    simpa only [Int.cast_natCast] using hB
  change (jacobiSym (a : ℤ) (n * m) : ℂ) =
    (jacobiSym ((y : ZMod n).val : ℤ) n : ℂ) * (jacobiSym ((z : ZMod m).val : ℤ) m : ℂ)
  rw [jacobiSym.mul_right, Int.cast_mul, hJ n hN, hJ m hM]

theorem jacobiTwistedUnitSum_chineseRemainder {n m : ℕ} [NeZero n] [NeZero m] (h : n.Coprime m)
    (u v a : ℤ) (huv : u * (m : ℤ) + v * (n : ℤ) = 1) :
    twistedSymmetricUnitSum (jacobiUnitWeight (n * m)) (a : ZMod (n * m)) =
      twistedSymmetricUnitSum (jacobiUnitWeight n) ((u * a : ℤ) : ZMod n) *
      twistedSymmetricUnitSum (jacobiUnitWeight m) ((v * a : ℤ) : ZMod m) := by
  rw [show jacobiUnitWeight (n * m) = fun x =>
    jacobiUnitWeight n (unitsChineseRemainder h x).1 *
      jacobiUnitWeight m (unitsChineseRemainder h x).2 from funext (jacobiUnitWeight_chineseRemainder h)]
  exact twistedSymmetricUnitSum_chineseRemainder h u v a huv _ _

theorem jacobiUnitWeight_prime_power {p r : ℕ} [Fact p.Prime] (hd : p ∣ p ^ r)
    (x : (ZMod (p ^ r))ˣ) :
    jacobiUnitWeight (p ^ r) x =
      primeQuadraticChar p (ZMod.castHom hd (ZMod p) (x : ZMod (p ^ r))) ^ r := by
  let f := ZMod.castHom hd (ZMod p)
  have hf : f (x : ZMod (p ^ r)) = ((x : ZMod (p ^ r)).val : ZMod p) := by
    calc
      _ = f (((x : ZMod (p ^ r)).val : ℕ) : ZMod (p ^ r)) := by rw [ZMod.natCast_zmod_val]
      _ = _ := map_natCast f _
  change (jacobiSym (((x : ZMod (p ^ r)).val : ℕ) : ℤ) (p ^ r) : ℂ) =
    primeQuadraticChar p (f (x : ZMod (p ^ r))) ^ r
  rw [jacobiSym.pow_right, ← legendreSym.to_jacobiSym, Int.cast_pow, primeQuadraticChar_apply, legendreSym,
    Int.cast_natCast, hf]

end
end ManuscriptAudit.Paper8JacobiWeightCRT

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8JacobiWeightCRT.jacobiTwistedUnitSum_chineseRemainder,
      ``ManuscriptAudit.Paper8JacobiWeightCRT.jacobiUnitWeight_prime_power] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
