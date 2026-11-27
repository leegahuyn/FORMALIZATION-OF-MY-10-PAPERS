import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianFrobeniusSquare
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! The actual characteristic-p torsion and p-adic Tate module are trivial in this family. -/

namespace ManuscriptAudit.Paper5NonsplitCharacteristicTorsion

open WeierstrassCurve WeierstrassFrobeniusFixed CubicThreeTorsionOrdinate
open Paper5NonsplitFrobeniusModFour CubicHermitianFrobeniusSquare
open PowerTorsionTower TorsionFrobeniusModule PowerTateModule

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

abbrev Points (A : ZMod p) := ((Curve A).baseChange L).Point

private theorem p_nsmul_eq_zero (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    {P : Points p L A} (hP : p • P = 0) : P = 0 := by
  let f := frobeniusOnPoints p L (Curve A)
  have hf : Function.Injective f :=
    Affine.Point.map_injective (W' := Curve A) (FiniteField.frobeniusAlgHom (ZMod p) L)
  have h₂ := (small_char p (ZMod p) hp).1
  have h₃ := (small_char p (ZMod p) hp).2
  have hq3 : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hq
  have hq2 : Fintype.card (ZMod p) % 2 = 1 := by
    apply FiniteField.odd_card_of_char_ne_two
    rw [ringChar.eq (ZMod p) p]
    omega
  have hSquare : f (f P) = -(p • P) := by
    simpa only [f, frobeniusOnPoints, ZMod.card] using
      frobenius_sq_eq_neg_card (ZMod p) L h₂ h₃ hA hq3 hq2 P
  apply hf
  apply hf
  rw [hSquare, hP, neg_zero, map_zero, map_zero]

theorem p_power_smul_eq_zero (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    {P : Points p L A} (n : ℕ) (h : (p ^ n) • P = 0) : P = 0 := by
  induction n with
  | zero => simpa only [pow_zero, one_nsmul] using h
  | succ n ih =>
    apply ih
    exact p_nsmul_eq_zero p L hp hq hA (by simpa only [pow_succ, mul_nsmul] using h)

theorem level_subsingleton (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) : Subsingleton (PowerTorsion p (Points p L A) n) := by
  refine ⟨fun P Q => Subtype.ext ?_⟩
  exact (p_power_smul_eq_zero p L hp hq hA n ((mem_iff _ _ _).mp P.property)).trans
    (p_power_smul_eq_zero p L hp hq hA n ((mem_iff _ _ _).mp Q.property)).symm

theorem level_card (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) : Nat.card (PowerTorsion p (Points p L A) n) = 1 := by
  letI := level_subsingleton p L hp hq hA n
  letI : Unique (PowerTorsion p (Points p L A) n) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact Nat.card_unique

theorem characteristic_tate_subsingleton (hp : 5 ≤ p) (hq : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) : Subsingleton (Tate p (Points p L A)) := by
  refine ⟨fun x y => PowerTateModule.ext p _ (fun n => ?_)⟩
  letI := level_subsingleton p L hp hq hA n
  exact Subsingleton.elim _ _

end
end ManuscriptAudit.Paper5NonsplitCharacteristicTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitCharacteristicTorsion.p_power_smul_eq_zero,
      ``ManuscriptAudit.Paper5NonsplitCharacteristicTorsion.level_subsingleton,
      ``ManuscriptAudit.Paper5NonsplitCharacteristicTorsion.level_card,
      ``ManuscriptAudit.Paper5NonsplitCharacteristicTorsion.characteristic_tate_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
