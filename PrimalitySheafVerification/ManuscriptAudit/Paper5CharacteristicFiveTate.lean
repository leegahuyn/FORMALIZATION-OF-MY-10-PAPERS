import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5CharacteristicFiveFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5TwoAdicFrobenius

/-! The actual prime-five Frobenius square on the compatible system of geometric two-power torsion. -/

namespace ManuscriptAudit.Paper5CharacteristicFiveTate

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open Paper5TwoPowerFrobenius Paper5TwoAdicFrobenius
open TwoPowerTateModule TorsionFrobeniusModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L] [IsAlgClosed L]

private theorem printedAffine_eq (A : ZMod 5) :
    Paper5FrobeniusModTwo.printedAffine 5 A = Curve A := by
  simp [Paper5FrobeniusModTwo.printedAffine, paper5TraceCurve, Curve, CubicAffine, shortCubic,
    ZMod.natCast_self]

private theorem point_square {A : ZMod 5} (hA : A ≠ 0) (P : GeometricPoints 5 L A) :
    pointFrobenius 5 L A (pointFrobenius 5 L A P) = -((5 : ℕ) • P) := by
  change WeierstrassFrobeniusFixed.frobeniusOnPoints 5 L _
      (WeierstrassFrobeniusFixed.frobeniusOnPoints 5 L _ P) = _
  revert P
  rw [printedAffine_eq]
  exact Paper5CharacteristicFiveFrobenius.frobenius_sq_eq_neg_five L hA

/-- The square of native Frobenius equals [-5] on the actual two-adic Tate module. -/
theorem square_on_tate {A : ZMod 5} (hA : A ≠ 0) (x : Tate (GeometricPoints 5 L A)) :
    frobenius 5 L (by decide) hA (frobenius 5 L (by decide) hA x) =
      -((5 : ℕ) : ℤ_[2]) • x := by
  rw [neg_smul, Nat.cast_smul_eq_nsmul]
  apply Subtype.ext
  funext n
  change evaluate _ n (frobenius 5 L (by decide) hA (frobenius 5 L (by decide) hA x)) =
    evaluate _ n (-((5 : ℕ) • x))
  rw [evaluate_frobenius, evaluate_frobenius, map_neg, map_nsmul]
  apply Subtype.ext
  exact point_square L hA (evaluate (GeometricPoints 5 L A) n x).val

end
end ManuscriptAudit.Paper5CharacteristicFiveTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5CharacteristicFiveTate.square_on_tate
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
