import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiWeightCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerReducedWeight

/-! Native CRT and local square-root estimates with one extra prime Jacobi factor. -/

namespace ManuscriptAudit.Paper8ExtraPrimeJacobi

open Paper8ZModAdditiveCRT Paper8OddCrossJacobiSum Paper8JacobiWeightCRT Paper8PrimeQuadraticPhase
open Paper8PrimePowerReducedWeight

noncomputable section

def extraPrimeJacobiUnitWeight (p M : ℕ) (x : (ZMod M)ˣ) : ℂ :=
  jacobiUnitWeight M x * (jacobiSym ((x : ZMod M).val : ℤ) p : ℂ)

theorem extraPrimeJacobiUnitWeight_chineseRemainder {p n m : ℕ} [NeZero n] [NeZero m]
    (h : n.Coprime m) (hp : p ∣ n) (x : (ZMod (n * m))ˣ) :
    extraPrimeJacobiUnitWeight p (n * m) x =
      extraPrimeJacobiUnitWeight p n (unitsChineseRemainder h x).1 *
      jacobiUnitWeight m (unitsChineseRemainder h x).2 := by
  let y := (unitsChineseRemainder h x).1
  let a := (x : ZMod (n * m)).val
  let b := (y : ZMod n).val
  let f := ZMod.castHom hp (ZMod p)
  have hX : (a : ZMod (n * m)) = x := ZMod.natCast_zmod_val _
  have hY : (ZMod.chineseRemainder h (a : ZMod (n * m))).1 = (y : ZMod n) := by rw [hX] <;> rfl
  rw [map_natCast (ZMod.chineseRemainder h)] at hY
  change (a : ZMod n) = y at hY
  have hB : (b : ZMod n) = (y : ZMod n) := ZMod.natCast_zmod_val _
  have hC : (a : ZMod p) = (b : ZMod p) := by
    have hh := congrArg f (hY.trans hB.symm)
    simpa only [map_natCast] using hh
  have hJ : jacobiSym (a : ℤ) p = jacobiSym (b : ℤ) p := by
    apply jacobiSym.mod_left'
    apply (ZMod.intCast_eq_intCast_iff' _ _ p).1
    simpa only [Int.cast_natCast] using hC
  unfold extraPrimeJacobiUnitWeight
  rw [jacobiUnitWeight_chineseRemainder h]
  change (_ * _) * (jacobiSym (a : ℤ) p : ℂ) = (_ * (jacobiSym (b : ℤ) p : ℂ)) * _
  rw [hJ]
  ring

theorem extraPrimeJacobiSum_chineseRemainder {p n m : ℕ} [NeZero n] [NeZero m] (h : n.Coprime m) (hp : p ∣ n)
    (u v a : ℤ) (hBez : u * (m : ℤ) + v * (n : ℤ) = 1) :
    twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight p (n * m)) (a : ZMod (n * m)) =
      twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight p n) ((u * a : ℤ) : ZMod n) *
      twistedSymmetricUnitSum (jacobiUnitWeight m) ((v * a : ℤ) : ZMod m) := by
  rw [show extraPrimeJacobiUnitWeight p (n * m) = fun x =>
    extraPrimeJacobiUnitWeight p n (unitsChineseRemainder h x).1 *
      jacobiUnitWeight m (unitsChineseRemainder h x).2 from
    funext (extraPrimeJacobiUnitWeight_chineseRemainder h hp)]
  exact twistedSymmetricUnitSum_chineseRemainder h u v a hBez _ _

theorem norm_extraPrimeJacobiSum_prime_power {p e : ℕ} [Fact p.Prime] [NeZero (p ^ e)]
    (hp : p ≠ 2) (he : 2 ≤ e) (a : ZMod (p ^ e)) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight p (p ^ e)) a‖ ≤ 2 * Real.sqrt ((p ^ e : ℕ) : ℝ) := by
  have hD : p ∣ p ^ e := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show e ≠ 0 by omega)
    refine ⟨p ^ j, ?_⟩
    rw [hj, pow_succ, mul_comm]
  let f := ZMod.castHom hD (ZMod p)
  let w (z : ZMod p) := primeQuadraticChar p z ^ e * primeQuadraticChar p z
  have hW : ∀ z, ‖w z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · simp [w, hz, primeQuadraticChar_apply]
    · simp [w, norm_mul, norm_pow, norm_primeQuadraticChar hz]
  have hWeight (x : (ZMod (p ^ e))ˣ) : extraPrimeJacobiUnitWeight p (p ^ e) x = primeReducedUnitWeight hD w x := by
    have hC : f (x : ZMod (p ^ e)) = ((x : ZMod (p ^ e)).val : ZMod p) := by
      calc
        _ = f (((x : ZMod (p ^ e)).val : ℕ) : ZMod (p ^ e)) := by rw [ZMod.natCast_zmod_val]
        _ = _ := map_natCast f _
    unfold extraPrimeJacobiUnitWeight primeReducedUnitWeight w
    rw [jacobiUnitWeight_prime_power hD, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
    simp only [primeQuadraticChar_apply, hC]
  rw [show extraPrimeJacobiUnitWeight p (p ^ e) = primeReducedUnitWeight hD w from funext hWeight]
  exact norm_prime_reduced_unit_sum hp he hD w hW a ha

end
end ManuscriptAudit.Paper8ExtraPrimeJacobi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExtraPrimeJacobi.extraPrimeJacobiSum_chineseRemainder,
      ``ManuscriptAudit.Paper8ExtraPrimeJacobi.norm_extraPrimeJacobiSum_prime_power] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
