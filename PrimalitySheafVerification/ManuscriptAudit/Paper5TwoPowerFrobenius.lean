import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective
import PrimalitySheafVerification.ManuscriptAudit.Paper5FrobeniusModTwo
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionCoordinateOperator

/-! Compatible actual Frobenius operators on the printed centered curve's geometric torsion tower. -/

namespace ManuscriptAudit.Paper5TwoPowerFrobenius

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open WeierstrassCurve CubicGeometricTorsion CubicDoublingSurjective
open Paper5FrobeniusModTwo TorsionFrobeniusModule
open TwoPowerTorsionCoordinateOperator

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]

abbrev GeometricPoints (A : ZMod p) := ((printedAffine p A).baseChange L).Point

theorem geometricDoublingSurj (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Function.Surjective (fun P : GeometricPoints p L A => (2 : ℕ) • P) := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have hsmall (n : ℕ) (h₀ : 0 < n) (hn : n < p) : (n : L) ≠ 0 :=
    (CharP.cast_eq_zero_iff L p n).not.mpr
      (fun h => (Nat.not_le_of_lt hn) (Nat.le_of_dvd h₀ h))
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega)
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)
  have hAL := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  change Function.Surjective (fun P : (((paper5TraceCurve p A).baseChange L).toProjective.toAffine).Point =>
    (2 : ℕ) • P)
  rw [printed_cubic_baseChange_eq_zero p A]
  exact affine_doubling_surjective h₂ h₃ hAL

theorem geometricTwoTorsionCard (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Nat.card (Torsion 2 (GeometricPoints p L A)) = 4 :=
  (Nat.card_congr (carrierEquiv 2 _)).trans
    ((Nat.card_congr (TwoTorsionFrobeniusModule.carrierEquiv _).symm).trans
      (geometricTwoTorsion_card p L hp hA))

abbrev pointFrobenius (A : ZMod p) : GeometricPoints p L A →+ GeometricPoints p L A :=
  WeierstrassFrobeniusFixed.frobeniusOnPoints p L (printedAffine p A)

def coordinateFrobenius (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    Coordinates n ≃ₗ[ZMod (2 ^ n)] Coordinates n :=
  automorphism _ (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA)
    (pointFrobenius p L A) (TwoTorsionFrobeniusModule.frobeniusOnPoints_injective p L _) n

theorem coordinateFrobenius_reduction (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) (v : Coordinates (n + 1)) :
    reducePair n (coordinateFrobenius p L hp hA (n + 1) v) =
      coordinateFrobenius p L hp hA n (reducePair n v) := by
  simpa only [coordinateFrobenius, automorphism_apply] using
    (operator_reduction _ (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA)
      (pointFrobenius p L A) n v)

theorem coordinateFrobenius_inverse_reduction (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) (v : Coordinates (n + 1)) :
    reducePair n ((coordinateFrobenius p L hp hA (n + 1)).symm v) =
      (coordinateFrobenius p L hp hA n).symm (reducePair n v) :=
  inverse_reduction _ (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA)
    (pointFrobenius p L A) (TwoTorsionFrobeniusModule.frobeniusOnPoints_injective p L _) n v

end
end ManuscriptAudit.Paper5TwoPowerFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5TwoPowerFrobenius.geometricDoublingSurj,
      ``ManuscriptAudit.Paper5TwoPowerFrobenius.geometricTwoTorsionCard,
      ``ManuscriptAudit.Paper5TwoPowerFrobenius.coordinateFrobenius_reduction,
      ``ManuscriptAudit.Paper5TwoPowerFrobenius.coordinateFrobenius_inverse_reduction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
