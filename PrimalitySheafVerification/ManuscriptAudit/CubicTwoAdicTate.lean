import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsion
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTateRankTwo

/-! The centered cubic's actual affine and projective 2-adic Tate modules. -/

namespace ManuscriptAudit.CubicTwoAdicTate

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicDoublingSurjective CubicTwoPowerTorsion TorsionFrobeniusModule
open TwoPowerTorsionTower TwoPowerTateModule TwoPowerTateRankTwo

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A : K}

def affinePadicCoordinates (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] Tate (Curve A).Point := by
  have hfour : Nat.card (Torsion 2 (Curve A).Point) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (by
      simpa only [pow_one] using affine_twoPower_card h₂ h₃ hA 1)
  exact padicPairEquiv _ (affine_doubling_surjective h₂ h₃ hA) hfour

def projectivePadicCoordinates (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    (ℤ_[2] × ℤ_[2]) ≃ₗ[ℤ_[2]] Tate (shortCubic (0 : K) A).toProjective.Point := by
  have hfour : Nat.card (Torsion 2 (shortCubic (0 : K) A).toProjective.Point) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (by
      simpa only [pow_one] using projective_twoPower_card h₂ h₃ hA 1)
  exact padicPairEquiv _ (projective_doubling_surjective h₂ h₃ hA) hfour

end
end ManuscriptAudit.CubicTwoAdicTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwoAdicTate.affinePadicCoordinates,
      ``ManuscriptAudit.CubicTwoAdicTate.projectivePadicCoordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
