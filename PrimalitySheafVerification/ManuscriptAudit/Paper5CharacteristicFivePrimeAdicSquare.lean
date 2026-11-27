import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5CharacteristicFiveFrobenius
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! The actual characteristic-five point identity on every native prime-adic inverse limit. -/

namespace ManuscriptAudit.Paper5CharacteristicFivePrimeAdicSquare

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace PowerTateModule TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L]

abbrev Points (A : ZMod 5) := (Curve (algebraMap (ZMod 5) L A)).Point

def pointFrobenius (A : ZMod 5) : AddMonoid.End (Points L A) :=
  pointMapAt (ZMod 5) L (Curve A) (Curve (algebraMap (ZMod 5) L A))
    (CubicNonsplitFrobeniusTrace.centered_baseChange (ZMod 5) L A)
    (FiniteField.frobeniusAlgHom (ZMod 5) L)

private theorem pointMapAt_sq {A : ZMod 5} (hA : A ≠ 0)
    {W : Affine L} (hW : (Curve A).baseChange L = W) (P : W.Point) :
    let f := pointMapAt (ZMod 5) L (Curve A) W hW (FiniteField.frobeniusAlgHom (ZMod 5) L)
    f (f P) = -((5 : ℕ) • P) := by
  subst W
  exact Paper5CharacteristicFiveFrobenius.frobenius_sq_eq_neg_five L hA P

theorem point_square {A : ZMod 5} (hA : A ≠ 0) (P : Points L A) :
    pointFrobenius L A (pointFrobenius L A P) = -((5 : ℕ) • P) :=
  pointMapAt_sq L hA (CubicNonsplitFrobeniusTrace.centered_baseChange (ZMod 5) L A) P

theorem square_on_tate (l : ℕ) [Fact l.Prime] {A : ZMod 5} (hA : A ≠ 0) (x : Tate l (Points L A)) :
    endMap l (pointFrobenius L A) (endMap l (pointFrobenius L A) x) =
      -((5 : ℕ) : ℤ_[l]) • x := by
  rw [neg_smul, Nat.cast_smul_eq_nsmul]
  apply PowerTateModule.ext l _
  intro n
  rw [evaluate_endMap, evaluate_endMap, map_neg, map_nsmul]
  apply Subtype.ext
  exact point_square L hA (evaluate l _ n x).val

end
end ManuscriptAudit.Paper5CharacteristicFivePrimeAdicSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5CharacteristicFivePrimeAdicSquare.point_square,
      ``ManuscriptAudit.Paper5CharacteristicFivePrimeAdicSquare.square_on_tate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
