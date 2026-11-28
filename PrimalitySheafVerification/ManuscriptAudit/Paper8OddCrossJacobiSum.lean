import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindOddSaliePhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModAdditiveCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff

/-! Exact Jacobi-twisted unit formula for the manuscript's cross sum at moduli coprime to six. -/

namespace ManuscriptAudit.Paper8OddCrossJacobiSum

open Finset Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence
open Paper8DedekindZeroReference Paper8OddCrossCuspPhase Paper8OddCrossPoincareKernel
open Paper8DedekindOddSaliePhase Paper8OddCrossCuspCutoff Paper8OddCrossCuspRows Paper8ZModAdditiveCRT

noncomputable section

def jacobiUnitWeight (k : ℕ) (x : (ZMod k)ˣ) : ℂ :=
  (jacobiSym (((x : ZMod k).val : ℕ) : ℤ) k : ℂ)

private theorem finEquiv_val {k : ℕ} [NeZero k] (d : Fin k) :
    (ZMod.finEquiv k d).val = d.val := by
  cases k with
  | zero => exact Fin.elim0 d
  | succ k => rfl

def reducedFinToUnit (k : ℕ) [NeZero k] : {d : Fin k // d.val.Coprime k} ≃ (ZMod k)ˣ :=
  ((ZMod.finEquiv k).toEquiv.subtypeEquiv (fun d => by
    change _ ↔ (ZMod.finEquiv k d).val.Coprime k
    rw [finEquiv_val])).trans (ZMod.unitsEquivCoprime).symm

theorem reducedFinToUnit_val {k : ℕ} [NeZero k] (d : {d : Fin k // d.val.Coprime k}) :
    ((reducedFinToUnit k d : (ZMod k)ˣ) : ZMod k).val = d.1.val := by
  change (((ZMod.finEquiv k d.1).val : ℕ) : ZMod k).val = d.1.val
  rw [ZMod.natCast_zmod_val, finEquiv_val]

private theorem alternate_odd_lift {k d : ℕ} [NeZero k] (hk : k % 2 = 1) :
    ∃ h : ℕ, h % 2 = 1 ∧ (h : ZMod k) = (d : ZMod k) ∧
      dedekindSum (h : ℤ) k = dedekindSum (d : ℤ) k := by
  by_cases hd : d % 2 = 1
  · exact ⟨d, hd, rfl, rfl⟩
  · refine ⟨d + k, by omega, ?_, ?_⟩
    · rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    · have h := dedekind_translate (Nat.pos_of_ne_zero (NeZero.ne k)) (d : ℤ) 1
      simpa only [Nat.cast_add, mul_one] using h

private theorem reference_entry_jacobi {k : ℕ} [NeZero k] (hk : k % 2 = 1) (h3 : ¬ (3 : ℕ) ∣ k)
    (d : {d : Fin k // d.val.Coprime k}) (u v : ℤ) (huv : 24 * u + (k : ℤ) * v = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (d.1.val : ℤ) k : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 24) *
        (jacobiUnitWeight k (reducedFinToUnit k d) *
          ZMod.stdAddChar ((u : ZMod k) *
            (((reducedFinToUnit k d : (ZMod k)ˣ) : ZMod k) +
              (((reducedFinToUnit k d)⁻¹ : (ZMod k)ˣ) : ZMod k)))) := by
  let x := reducedFinToUnit k d
  let a : ℤ := (((x⁻¹ : (ZMod k)ˣ) : ZMod k).val : ℕ)
  have hA : (a : ZMod k) = ((x⁻¹ : (ZMod k)ˣ) : ZMod k) := by
    dsimp only [a]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hD : (d.1.val : ZMod k) = x := by rw [← reducedFinToUnit_val d, ZMod.natCast_zmod_val]
  obtain ⟨h, hh, hCast, hDed⟩ := alternate_odd_lift (d := d.1.val) hk
  have hX : (h : ZMod k) = x := hCast.trans hD
  have hC : h.Coprime k := (ZMod.isUnit_iff_coprime h k).1 (by rw [hX]; exact x.isUnit)
  have hInv : (h : ZMod k) * (a : ZMod k) = 1 := by
    rw [hX, hA]
    exact x.mul_inv
  have hJ : jacobiSym (h : ℤ) k = jacobiSym (d.1.val : ℤ) k := by
    apply jacobiSym.mod_left'
    apply (ZMod.intCast_eq_intCast_iff' _ _ k).1
    simpa only [Int.cast_natCast] using hCast
  have hChar : (jacobiSym (h : ℤ) k : ℂ) = jacobiUnitWeight k x := by
    unfold jacobiUnitWeight x
    rw [reducedFinToUnit_val, hJ]
  have hPhase : exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (k : ℂ)) =
      ZMod.stdAddChar ((u : ZMod k) * ((x : ZMod k) + ((x⁻¹ : (ZMod k)ˣ) : ZMod k))) := by
    have hE : ZMod.stdAddChar ((u * ((h : ℤ) + a) : ℤ) : ZMod k) =
        exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (k : ℂ)) := by
      rw [ZMod.stdAddChar_coe, exponentialPhase]
      congr 1
      ring
    rw [← hE]
    congr 1
    push_cast
    rw [hX, hA]
  have hTerm := dedekind_odd_coprime_six_summand hh hk h3 hC u v a huv hInv
  rw [hDed, hChar, hPhase] at hTerm
  simpa only [mul_assoc, x] using hTerm

theorem referenceZeroSum_eq_jacobi_unit_sum {k : ℕ} [NeZero k] (hk : k % 2 = 1)
    (h3 : ¬ (3 : ℕ) ∣ k) (u v : ℤ) (huv : 24 * u + (k : ℤ) * v = 1) :
    referenceZeroSum k =
      exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 24) *
        twistedSymmetricUnitSum (jacobiUnitWeight k) (u : ZMod k) := by
  unfold referenceZeroSum twistedSymmetricUnitSum
  rw [Finset.sum_subtype (p := fun d : Fin k => d.val.Coprime k) _ (by simp), Finset.mul_sum]
  apply Fintype.sum_equiv (reducedFinToUnit k) _ _
  intro d
  exact reference_entry_jacobi hk h3 d u v huv

theorem crossSum_eq_jacobi_unit_sum {k : ℕ} [NeZero k] (hk : k % 2 = 1)
    (h3 : ¬ (3 : ℕ) ∣ k) (u v : ℤ) (huv : 24 * u + (k : ℤ) * v = 1) :
    crossSum (Nat.pos_of_ne_zero (NeZero.ne k)) =
      (chiFour (k : ZMod 4) : ℂ) *
        exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 24) *
        twistedSymmetricUnitSum (jacobiUnitWeight k) (u : ZMod k) := by
  rw [crossSum_eq, referenceZeroSum_eq_jacobi_unit_sum hk h3 u v huv, mul_assoc]

end
end ManuscriptAudit.Paper8OddCrossJacobiSum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossJacobiSum.crossSum_eq_jacobi_unit_sum
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
