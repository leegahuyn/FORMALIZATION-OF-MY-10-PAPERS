import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5TwoPowerFrobenius
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTateAutomorphism
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTateRankTwo

/-! The native arithmetic Frobenius on actual centered-cubic 2-adic Tate modules. -/

namespace ManuscriptAudit.Paper5TwoAdicFrobenius

open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTateModule
open TwoPowerTateAutomorphism TwoPowerTateRankTwo Paper5TwoPowerFrobenius

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]

def padicCoordinates (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] Tate (GeometricPoints p L A) :=
  padicPairEquiv _ (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA)

def frobenius (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Tate (GeometricPoints p L A) ≃ₗ[ℤ_[2]] Tate (GeometricPoints p L A) :=
  mapEquiv (pointFrobenius p L A)
    (TwoTorsionFrobeniusModule.frobeniusOnPoints_injective p L _) fun n =>
    Nat.finite_of_card_ne_zero (by
      rw [card_powerTorsion _ (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA)]
      exact pow_ne_zero _ (by decide : (4 : ℕ) ≠ 0))

theorem evaluate_frobenius (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) (x : Tate (GeometricPoints p L A)) :
    evaluate _ n (frobenius p L hp hA x) = mapLinear (2 ^ n) (pointFrobenius p L A)
      (evaluate _ n x) := rfl

def coordinateFrobeniusPadic (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] (ℤ_[2] × ℤ_[2]) :=
  ((padicCoordinates p L hp hA).trans (frobenius p L hp hA)).trans
    (padicCoordinates p L hp hA).symm

def residuePair (n : ℕ) (a : ℤ_[2] × ℤ_[2]) :
    TwoPowerTorsionCoordinateOperator.Coordinates n :=
  (PadicInt.toZModPow n a.1, PadicInt.toZModPow n a.2)

theorem residue_coordinateFrobenius (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) (a : ℤ_[2] × ℤ_[2]) :
    residuePair n (coordinateFrobeniusPadic p L hp hA a) =
      coordinateFrobenius p L hp hA n (residuePair n a) := by
  let h := geometricDoublingSurj p L hp hA
  let hfour := geometricTwoTorsionCard p L hp hA
  let e := TwoPowerTorsionCompatibleBasis.compatibleLevelEquiv (GeometricPoints p L A) h hfour n
  apply e.injective
  have hl : padicCoordinates p L hp hA (coordinateFrobeniusPadic p L hp hA a) =
      frobenius p L hp hA (padicCoordinates p L hp hA a) := by
    change padicCoordinates p L hp hA
      ((padicCoordinates p L hp hA).symm (frobenius p L hp hA (padicCoordinates p L hp hA a))) = _
    exact (padicCoordinates p L hp hA).apply_symm_apply _
  have hlev := congrArg (evaluate (GeometricPoints p L A) n) hl
  change e (residuePair n (coordinateFrobeniusPadic p L hp hA a)) =
    mapLinear (2 ^ n) (pointFrobenius p L A) (e (residuePair n a)) at hlev
  exact hlev.trans
    (TwoPowerTorsionCoordinateOperator.operator_apply _ h hfour (pointFrobenius p L A) n _).symm

end
end ManuscriptAudit.Paper5TwoAdicFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5TwoAdicFrobenius.padicCoordinates,
      ``ManuscriptAudit.Paper5TwoAdicFrobenius.frobenius,
      ``ManuscriptAudit.Paper5TwoAdicFrobenius.evaluate_frobenius,
      ``ManuscriptAudit.Paper5TwoAdicFrobenius.residue_coordinateFrobenius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
