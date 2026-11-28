import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8UnitReductionThree
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossJacobiSum

/-! Actual cross-cusp Jacobi sum at odd multiples of three, including the exact three-to-one lift. -/

namespace ManuscriptAudit.Paper8OddCrossThreeSum

open Finset Paper8ContourResidueWeights Paper8OddCrossCuspPhase Paper8DedekindOddSaliePhase
open Paper8OddCrossJacobiSum Paper8OddCrossCuspCutoff Paper8OddCrossCuspRows Paper8OddCrossPoincareKernel
open Paper8DedekindZeroReference Paper8DedekindKloostermanCongruence
open Paper8UnitReductionThree Paper8ProductStationaryPhase Paper8ZModAdditiveCRT

noncomputable section

def jacobiLiftWeight (k : ℕ) (x : (ZMod (3 * k))ˣ) : ℂ :=
  (jacobiSym ((reduceLowDigit (x : ZMod (3 * k)) : ZMod k).val : ℤ) k : ℂ)

private theorem exists_odd_nat_cast {n : ℕ} [NeZero n] (hn : n % 2 = 1) (z : ZMod n) :
    ∃ h : ℕ, h % 2 = 1 ∧ (h : ZMod n) = z := by
  by_cases hz : z.val % 2 = 1
  · exact ⟨z.val, hz, ZMod.natCast_zmod_val z⟩
  · refine ⟨z.val + n, by omega, ?_⟩
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

private theorem dedekindSum_eq_of_zmodCast {n : ℕ} (hn : 0 < n) {a b : ℤ}
    (h : (a : ZMod n) = (b : ZMod n)) : dedekindSum a n = dedekindSum b n := by
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).1 h.symm
  have ht : a = b + (n : ℤ) * q := by omega
  rw [ht, dedekind_translate hn]

private theorem referenceZeroSum_units {k : ℕ} [NeZero k] :
    referenceZeroSum k = ∑ x : (ZMod k)ˣ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum ((x : ZMod k).val : ℤ) k : ℝ) : ℂ)) := by
  unfold referenceZeroSum
  rw [Finset.sum_subtype (p := fun d : Fin k => d.val.Coprime k) _ (by simp)]
  apply Fintype.sum_equiv (reducedFinToUnit k) _ _
  intro d
  rw [reducedFinToUnit_val]

theorem referenceZeroSum_eq_lifted_jacobi_sum {k : ℕ} [NeZero k] (hk : k % 2 = 1)
    (h3 : 3 ∣ k) (u v : ℤ) (huv : 8 * u + (3 * (k : ℤ)) * v = 1) :
    referenceZeroSum k =
      (1 / 3 : ℂ) * exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 8) *
        twistedSymmetricUnitSum (jacobiLiftWeight k) (u : ZMod (3 * k)) := by
  let M := 3 * k
  let f := @reduceLowDigit 3 k
  let E := exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 8)
  have hM : M % 2 = 1 := by unfold M; simpa only [Nat.mul_mod, hk]
  let F (z : ZMod k) := Complex.exp ((Real.pi : ℂ) * Complex.I *
    ((dedekindSum (z.val : ℤ) k : ℝ) : ℂ))
  have hTerm (x : (ZMod M)ˣ) : F (f (x : ZMod M)) = E * (jacobiLiftWeight k x *
      ZMod.stdAddChar ((u : ZMod M) * ((x : ZMod M) + ((x⁻¹ : (ZMod M)ˣ) : ZMod M)))) := by
    let z := f (x : ZMod M)
    let a : ℤ := ((x⁻¹ : (ZMod M)ˣ) : ZMod M).val
    obtain ⟨h, hh, hX⟩ := exists_odd_nat_cast hM (x : ZMod M)
    have hL : (h : ZMod k) = z := by
      have h := congrArg f hX
      rw [map_natCast] at h
      exact h
    have hC : h.Coprime k := (ZMod.isUnit_iff_coprime h k).1 (by rw [hL]; exact x.isUnit.map f)
    have hA : (a : ZMod M) = ((x⁻¹ : (ZMod M)ˣ) : ZMod M) := by
      dsimp only [a]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hInv : (h : ZMod M) * (a : ZMod M) = 1 := by
      rw [hX, hA]
      exact x.mul_inv
    have hZ : ((h : ℤ) : ZMod k) = ((z.val : ℤ) : ZMod k) := by
      rw [Int.cast_natCast, Int.cast_natCast, hL, ZMod.natCast_zmod_val]
    have hDed := dedekindSum_eq_of_zmodCast (Nat.pos_of_ne_zero (NeZero.ne k)) hZ
    have hJ : jacobiSym (h : ℤ) k = jacobiSym (z.val : ℤ) k :=
      jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ k).1 hZ)
    have hPh : exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (3 * (k : ℂ))) =
        ZMod.stdAddChar ((u : ZMod M) * ((x : ZMod M) + ((x⁻¹ : (ZMod M)ˣ) : ZMod M))) := by
      have hP : exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (3 * (k : ℂ))) =
          ZMod.stdAddChar ((u * ((h : ℤ) + a) : ℤ) : ZMod M) := by
        rw [exponentialPhase, ZMod.stdAddChar_coe]
        unfold M
        push_cast
        congr 1
        ring
      rw [hP]
      congr 1
      push_cast
      rw [hX, hA]
    have hS := dedekind_odd_multiple_three_summand hh hk h3 hC u v a huv hInv
    rw [hDed, hJ, hPh, mul_assoc] at hS
    exact hS
  have hF : (∑ x : (ZMod M)ˣ, F (f (x : ZMod M))) = E * twistedSymmetricUnitSum (jacobiLiftWeight k) (u : ZMod M) := by
    unfold twistedSymmetricUnitSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => hTerm x)
  have hS := sum_units_three_lifts h3 F
  change (∑ x : (ZMod M)ˣ, F (f (x : ZMod M))) = 3 * ∑ x : (ZMod k)ˣ, F x at hS
  rw [hF, ← referenceZeroSum_units] at hS
  change referenceZeroSum k = (1 / 3 : ℂ) * E * twistedSymmetricUnitSum (jacobiLiftWeight k) (u : ZMod M)
  linear_combination -(1 / 3 : ℂ) * hS

theorem crossSum_eq_lifted_jacobi_sum {k : ℕ} [NeZero k] (hk : k % 2 = 1)
    (h3 : 3 ∣ k) (u v : ℤ) (huv : 8 * u + (3 * (k : ℤ)) * v = 1) :
    crossSum (Nat.pos_of_ne_zero (NeZero.ne k)) =
      (chiFour (k : ZMod 4) : ℂ) * (1 / 3 : ℂ) *
        exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 8) *
        twistedSymmetricUnitSum (jacobiLiftWeight k) (u : ZMod (3 * k)) := by
  rw [crossSum_eq, referenceZeroSum_eq_lifted_jacobi_sum hk h3 u v huv]
  ring

end
end ManuscriptAudit.Paper8OddCrossThreeSum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossThreeSum.crossSum_eq_lifted_jacobi_sum
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
