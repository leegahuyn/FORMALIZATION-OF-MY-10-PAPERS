import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingSurjective
import PrimalitySheafVerification.ManuscriptAudit.PowerTateRankTwo

/-! The genuine 3-adic Tate modules of the nonsingular centered cubic. -/

namespace ManuscriptAudit.CubicThreeAdicTate

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicThreeTorsionBasis CubicTriplingSurjective PowerTorsionTower PowerTateModule PowerTateRankTwo

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A : K}

private def firstBasis (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Module.Basis (Fin 2) (ZMod (3 ^ 1)) (PowerTorsion 3 (Curve A).Point 1) :=
  basis h₂ h₃ hA (Classical.choice (flexPair_nonempty h₂ hA))

def affinePadicCoordinates (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    (ℤ_[3] × ℤ_[3]) ≃ₗ[ℤ_[3]] Tate 3 (Curve A).Point :=
  padicPairEquiv 3 _ (firstBasis h₂ h₃ hA) (affine_tripling_surjective h₂ h₃ hA)

def projectivePadicCoordinates (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    (ℤ_[3] × ℤ_[3]) ≃ₗ[ℤ_[3]] Tate 3 (shortCubic (0 : K) A).toProjective.Point :=
  (affinePadicCoordinates h₂ h₃ hA).trans
    (mapAddEquiv 3 (Projective.Point.toAffineAddEquiv
      (W := (shortCubic (0 : K) A).toProjective))).symm

theorem affine_threePower_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (n : ℕ) : Nat.card (PowerTorsion 3 (Curve A).Point n) = 9 ^ n := by
  rw [card_powerTorsion 3 _ (affine_tripling_surjective h₂ h₃ hA), card_torsion h₂ h₃ hA]

end
end ManuscriptAudit.CubicThreeAdicTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeAdicTate.affinePadicCoordinates,
      ``ManuscriptAudit.CubicThreeAdicTate.projectivePadicCoordinates,
      ``ManuscriptAudit.CubicThreeAdicTate.affine_threePower_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
