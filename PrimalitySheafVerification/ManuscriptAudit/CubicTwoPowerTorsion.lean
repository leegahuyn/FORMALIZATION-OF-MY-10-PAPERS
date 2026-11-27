import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicGeneralTwoTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionTower

/-! Exact cardinalities and transition maps on the centered cubic's actual geometric two-power torsion. -/

namespace ManuscriptAudit.CubicTwoPowerTorsion

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicDoublingSurjective TorsionFrobeniusModule TwoPowerTorsionTower

noncomputable section

section Centered

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A : K}

theorem affine_twoPower_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (n : ℕ) : Nat.card {P : (Curve A).Point // (2 ^ n : ℕ) • P = 0} = 4 ^ n := by
  have hfour : Nat.card (Torsion 2 (Curve A).Point) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans
      (CubicGeneralTwoTorsionCard.affineTwoTorsion_card h₂
        (shortCubic_discriminant_ne_zero h₂ h₃ hA))
  exact (Nat.card_congr (carrierEquiv (2 ^ n) _).symm).trans
    (card_powerTorsion _ (affine_doubling_surjective h₂ h₃ hA) hfour n)

theorem projective_twoPower_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (n : ℕ) :
    Nat.card {P : (shortCubic (0 : K) A).toProjective.Point // (2 ^ n : ℕ) • P = 0} = 4 ^ n := by
  let G := (shortCubic (0 : K) A).toProjective.Point
  have hfour : Nat.card (Torsion 2 G) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans
      (CubicGeneralTwoTorsionCard.projectiveTwoTorsion_card h₂
        (shortCubic_discriminant_ne_zero h₂ h₃ hA))
  exact (Nat.card_congr (carrierEquiv (2 ^ n) _).symm).trans
    (card_powerTorsion G (projective_doubling_surjective h₂ h₃ hA) hfour n)

theorem projective_transition_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (n : ℕ) :
    Function.Surjective (transition (shortCubic (0 : K) A).toProjective.Point n) :=
  transition_surjective _ (projective_doubling_surjective h₂ h₃ hA) n

theorem projective_transition_kernel_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (n : ℕ) :
    Nat.card (transition (shortCubic (0 : K) A).toProjective.Point n).ker = 4 :=
  (Nat.card_congr (transitionKernelEquiv _ n)).trans
    ((Nat.card_congr (carrierEquiv 2 _)).trans
      (CubicGeneralTwoTorsionCard.projectiveTwoTorsion_card h₂
        (shortCubic_discriminant_ne_zero h₂ h₃ hA)))

end Centered

/-- The compatible Frobenius maps act on the actual affine point tower over the prime field. -/
theorem frobenius_transition (p : ℕ) [Fact p.Prime] (L : Type*) [Field L]
    [Algebra (ZMod p) L] [DecidableEq L] (W : Affine (ZMod p))
    (n : ℕ) (P : PowerTorsion (W.baseChange L).Point (n + 1)) :
    transition (W.baseChange L).Point n ((frobeniusLinear (2 ^ (n + 1)) p L W) P) =
      (frobeniusLinear (2 ^ n) p L W) (transition (W.baseChange L).Point n P) :=
  map_transition (WeierstrassFrobeniusFixed.frobeniusOnPoints p L W) n P

end
end ManuscriptAudit.CubicTwoPowerTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwoPowerTorsion.affine_twoPower_card,
      ``ManuscriptAudit.CubicTwoPowerTorsion.projective_twoPower_card,
      ``ManuscriptAudit.CubicTwoPowerTorsion.projective_transition_surjective,
      ``ManuscriptAudit.CubicTwoPowerTorsion.projective_transition_kernel_card,
      ``ManuscriptAudit.CubicTwoPowerTorsion.frobenius_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
