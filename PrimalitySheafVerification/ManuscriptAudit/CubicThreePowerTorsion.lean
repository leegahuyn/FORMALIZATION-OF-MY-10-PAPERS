import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeRotationCyclicBasis
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionLift

/-! The centered geometric cubic has genuine finite three-power levels and cyclic rotation bases. -/

namespace ManuscriptAudit.CubicThreePowerTorsion

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicThreeTorsionBasis CubicTriplingSurjective CubicThreeRotationCyclicBasis
open TorsionFrobeniusModule PowerTorsionTower PowerTorsionLift

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] {A z : K}

theorem affine_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (n : ℕ) :
    Nat.card (PowerTorsion 3 (Curve A).Point n) = 9 ^ n := by
  rw [card_powerTorsion 3 (Curve A).Point (affine_tripling_surjective h₂ h₃ hA) n,
    CubicThreeTorsionBasis.card_torsion h₂ h₃ hA]

theorem projective_card (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (n : ℕ) :
    Nat.card (PowerTorsion 3 (shortCubic (0 : K) A).toProjective.Point n) = 9 ^ n := by
  rw [card_powerTorsion 3 _ (projective_tripling_surjective h₂ h₃ hA) n]
  have h := (Nat.card_congr (carrierEquiv 3 (shortCubic (0 : K) A).toProjective.Point)).trans
    (CubicThreeTorsionCard.projectiveThreeTorsion_card_of_coefficients h₂ h₃ hA)
  rw [h]

/-- Every positive native three-power level has a two-element basis cycled by the cube root. -/
theorem exists_cyclic_basis (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (n : ℕ) :
    ∃ B : Module.Basis (Fin 2) (ZMod (3 ^ (n + 1))) (PowerTorsion 3 (Curve A).Point (n + 1)),
      rotation h₂ h₃ hA hz (3 ^ (n + 1)) (B 0) = B 1 := by
  classical
  let G := (Curve A).Point
  let D := Classical.choice (flexPair_nonempty h₂ hA)
  let T := horizontal h₂ h₃ hA D
  let h := affine_tripling_surjective h₂ h₃ hA
  let P := lifted 3 G h T n
  exact exists_cyclic_basis_of_lift h₂ h₃ hA hz hz₁ D n
    (affine_card h₂ h₃ hA (n + 1)) P (scale_lifted 3 G h T n)

theorem affine_transition_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (n : ℕ) :
    Function.Surjective (transition 3 (Curve A).Point n) :=
  transition_surjective 3 (Curve A).Point (affine_tripling_surjective h₂ h₃ hA) n

end
end ManuscriptAudit.CubicThreePowerTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreePowerTorsion.affine_card,
      ``ManuscriptAudit.CubicThreePowerTorsion.projective_card,
      ``ManuscriptAudit.CubicThreePowerTorsion.exists_cyclic_basis,
      ``ManuscriptAudit.CubicThreePowerTorsion.affine_transition_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
