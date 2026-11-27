import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5TwoAdicCoefficients

/-! The actual 2-adic Frobenius trace of the centered curve is zero in the nonsplit case. -/

namespace ManuscriptAudit.Paper5NonsplitTwoAdicTrace

open WeierstrassCurve FiniteFieldPointCount
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open Paper5TwoPowerFrobenius Paper5TwoAdicCoefficients
open TorsionFrobeniusModule TwoPowerTorsionCompatibleBasis TwoPowerTorsionCoordinateOperator

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]

theorem coordinate_trace_eq_native (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    LinearMap.trace (ZMod (2 ^ n)) (Coordinates n) (coordinateFrobenius p L hp hA n).toLinearMap =
      LinearMap.trace (ZMod (2 ^ n)) (TwoPowerTorsionTower.PowerTorsion ((Curve A).baseChange L).Point n)
        (actualFrobenius (ZMod p) L A n) := by
  let e := compatibleLevelEquiv (GeometricPoints p L A)
    (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA) n
  change LinearMap.trace (ZMod (2 ^ n)) (Coordinates n)
    (e.symm.conj (mapLinear (2 ^ n) (pointFrobenius p L A))) = _
  rw [LinearMap.trace_conj']
  have hW : Paper5FrobeniusModTwo.printedAffine p A = Curve A := by
    change (paper5TraceCurve p A).toProjective.toAffine =
      (shortCubic (0 : ZMod p) A).toProjective.toAffine
    apply congrArg (fun W : WeierstrassCurve (ZMod p) => W.toProjective.toAffine)
    simp [paper5TraceCurve, shortCubic, ZMod.natCast_self]
  exact congrArg (fun W : Affine (ZMod p) =>
    LinearMap.trace (ZMod (2 ^ n)) (TwoPowerTorsionTower.PowerTorsion (W.baseChange L).Point n)
      (pointMap (2 ^ n) W (FiniteField.frobeniusAlgHom (ZMod p) L))) hW

theorem trace_eq_zero (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hq : p % 3 = 2) :
    trace p L hp hA = 0 := by
  apply trace_eq_of_reductions
  intro n
  rw [map_zero, coordinate_trace_eq_native p L hp hA n]
  have hsmall (n : ℕ) (h₀ : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p n).not.mpr
      (fun h => (Nat.not_le_of_lt hn) (Nat.le_of_dvd h₀ h))
  have h₂ : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega)
  have h₃ : (3 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)
  have hq' : Fintype.card (ZMod p) % 3 = 2 := by rw [ZMod.card]; exact hq
  exact (actual_trace_zero (ZMod p) L h₂ h₃ hA hq' n).symm

end
end ManuscriptAudit.Paper5NonsplitTwoAdicTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitTwoAdicTrace.coordinate_trace_eq_native,
      ``ManuscriptAudit.Paper5NonsplitTwoAdicTrace.trace_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
