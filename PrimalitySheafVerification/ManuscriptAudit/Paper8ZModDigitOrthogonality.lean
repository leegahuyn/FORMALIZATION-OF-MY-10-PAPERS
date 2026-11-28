import Lean.Util.CollectAxioms
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! Exact digit decomposition and additive cancellation over the high digit of a product modulus. -/

namespace ManuscriptAudit.Paper8ZModDigitOrthogonality

open Finset AddChar

noncomputable section

def residueDigitEquiv (n m : ℕ) [NeZero n] [NeZero m] :
    ZMod n × ZMod m ≃ ZMod (n * m) :=
  (((ZMod.finEquiv n).toEquiv.symm.prodCongr (ZMod.finEquiv m).toEquiv.symm).trans
    finProdFinEquiv).trans (ZMod.finEquiv (n * m)).toEquiv

private theorem val_finEquiv {m : ℕ} [NeZero m] (a : Fin m) :
    (ZMod.finEquiv m a).val = a.val := by
  cases m with
  | zero => exact Fin.elim0 a
  | succ m => rfl

private theorem val_finEquiv_symm {m : ℕ} [NeZero m] (a : ZMod m) :
    ((ZMod.finEquiv m).toEquiv.symm a).val = a.val := by
  let e := (ZMod.finEquiv m).toEquiv
  have h := val_finEquiv (e.symm a)
  change (e (e.symm a)).val = (e.symm a).val at h
  rw [e.apply_symm_apply] at h
  exact h.symm

theorem residueDigitEquiv_apply {n m : ℕ} [NeZero n] [NeZero m] (a : ZMod n) (b : ZMod m) :
    residueDigitEquiv n m (a, b) = ((b.val + m * a.val : ℕ) : ZMod (n * m)) := by
  let ia := (ZMod.finEquiv n).toEquiv.symm a
  let ib := (ZMod.finEquiv m).toEquiv.symm b
  let d := finProdFinEquiv (ia, ib)
  have hd : d.val = ib.val + m * ia.val := rfl
  change ZMod.finEquiv (n * m) d = _
  have h := (ZMod.natCast_zmod_val (ZMod.finEquiv (n * m) d)).symm
  have hIA : ia.val = a.val := val_finEquiv_symm a
  have hIB : ib.val = b.val := val_finEquiv_symm b
  rw [val_finEquiv d, hd, hIA, hIB] at h
  exact h

theorem sum_residue_digits {n m : ℕ} [NeZero n] [NeZero m] {E : Type*} [AddCommMonoid E]
    (F : ZMod (n * m) → E) :
    (∑ z : ZMod (n * m), F z) =
      ∑ a : ZMod n, ∑ b : ZMod m, F (((b.val + m * a.val : ℕ) : ZMod (n * m))) := by
  calc
    _ = ∑ ab : ZMod n × ZMod m, F (residueDigitEquiv n m ab) :=
      (Fintype.sum_equiv (residueDigitEquiv n m) _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]; simp_rw [residueDigitEquiv_apply]

def reduceHighDigit {n m : ℕ} : ZMod (n * m) →+* ZMod n :=
  ZMod.castHom (dvd_mul_right n m) (ZMod n)

theorem reduceHighDigit_apply {n m : ℕ} [NeZero n] [NeZero m] (z : ZMod (n * m)) :
    reduceHighDigit z = (z.val : ZMod n) := by
  calc
    _ = reduceHighDigit ((z.val : ℕ) : ZMod (n * m)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast reduceHighDigit _

theorem stdAddChar_high_digit {n m : ℕ} [NeZero n] [NeZero m] (z : ZMod (n * m)) (a : ZMod n) :
    ZMod.stdAddChar ((m : ZMod (n * m)) * z * (a.val : ZMod (n * m))) =
      ZMod.stdAddChar (reduceHighDigit z * a) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  calc
    _ = ZMod.stdAddChar (((((m : ℤ) * (z.val : ℤ) * (a.val : ℤ)) : ℤ) : ZMod (n * m))) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℤ) * (z.val : ℤ) * (a.val : ℤ) : ℤ) : ℂ) /
        ((n * m : ℕ) : ℂ)) := ZMod.stdAddChar_coe _
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((z.val : ℤ) * (a.val : ℤ) : ℤ) : ℂ) / (n : ℂ)) := by
      congr 1
      push_cast
      field_simp [hn, hm] <;> ring
    _ = ZMod.stdAddChar (((((z.val : ℤ) * (a.val : ℤ)) : ℤ) : ZMod n)) := (ZMod.stdAddChar_coe _).symm
    _ = _ := by
      push_cast
      rw [reduceHighDigit_apply, ZMod.natCast_zmod_val]

theorem sum_stdAddChar_high_digit {n m : ℕ} [NeZero n] [NeZero m] (z : ZMod (n * m)) :
    (∑ a : ZMod n, ZMod.stdAddChar ((m : ZMod (n * m)) * z * (a.val : ZMod (n * m)))) =
      if reduceHighDigit z = 0 then (n : ℂ) else 0 := by
  simp_rw [stdAddChar_high_digit, mul_comm (reduceHighDigit z)]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]

end
end ManuscriptAudit.Paper8ZModDigitOrthogonality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ZModDigitOrthogonality.sum_residue_digits,
      ``ManuscriptAudit.Paper8ZModDigitOrthogonality.sum_stdAddChar_high_digit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
