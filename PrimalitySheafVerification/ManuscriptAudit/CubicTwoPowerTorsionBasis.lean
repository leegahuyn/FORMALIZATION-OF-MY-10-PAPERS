import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsion
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionBasis

/-! Actual free bases of the centered cubic's affine and projective geometric two-power torsion. -/

namespace ManuscriptAudit.CubicTwoPowerTorsionBasis

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicDoublingSurjective CubicTwoPowerTorsion TorsionFrobeniusModule
open TwoPowerTorsionTower TwoPowerTorsionBasis

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A : K}

/-- Basis over ZMod(2^n) on the subgroup of actual affine points killed by 2^n. -/
def affineBasis (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ n)) (PowerTorsion (Curve A).Point n) := by
  have hfour : Nat.card (Torsion 2 (Curve A).Point) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (by
      simpa only [pow_one] using affine_twoPower_card h₂ h₃ hA 1)
  exact levelBasis _ (affine_doubling_surjective h₂ h₃ hA) hfour n

/-- Basis over ZMod(2^n) on the subgroup of actual projective points killed by 2^n. -/
def projectiveBasis (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ n))
      (PowerTorsion (shortCubic (0 : K) A).toProjective.Point n) := by
  have hfour : Nat.card (Torsion 2 (shortCubic (0 : K) A).toProjective.Point) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (by
      simpa only [pow_one] using projective_twoPower_card h₂ h₃ hA 1)
  exact levelBasis _ (projective_doubling_surjective h₂ h₃ hA) hfour n

end
end ManuscriptAudit.CubicTwoPowerTorsionBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwoPowerTorsionBasis.affineBasis,
      ``ManuscriptAudit.CubicTwoPowerTorsionBasis.projectiveBasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
