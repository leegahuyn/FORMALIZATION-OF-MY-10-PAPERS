import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalCMOperations

/-! Integral scalar minus cube rotation is a field-natural additive operation. -/

namespace ManuscriptAudit.CubicNaturalShiftedRotation

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicNaturalPointEnd CubicNaturalCMOperations CubicNativePointBaseChange
open CubicCubeRotation

noncomputable section
open scoped Classical

universe u

variable {K : Type u} [Field K] {A z : K}

/-- The actual operation [c]−ρ on every extension. -/
def shifted (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hz : z ^ 3 = 1)
    (c : ℤ) : Family K A where
  atField L := c • (1 : AddMonoid.End (GeometricPoints K L A)) - (rotation h₂ h₃ hA hz).atField L
  commute := by
    intro L M _ _ _ _ _ _ g P
    let R := rotation h₂ h₃ hA hz
    change pointsMap A g (c • P - R.atField L P) =
      c • pointsMap A g P - R.atField M (pointsMap A g P)
    rw [map_sub, map_zsmul, R.commute]

/-- The rotation acts on an actual affine point by multiplying its abscissa by z. -/
theorem rotation_some (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hz : z ^ 3 = 1)
    {L : Type u} [Field L] [DecidableEq L] [Algebra K L] {x y : L}
    (h : (Curve (algebraMap K L A)).Nonsingular x y) :
    ∃ h' : (Curve (algebraMap K L A)).Nonsingular (algebraMap K L z * x) y,
      (rotation h₂ h₃ hA hz).atField L (.some x y h) = .some (algebraMap K L z * x) y h' := by
  exact ⟨_, rfl⟩

end

end ManuscriptAudit.CubicNaturalShiftedRotation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicNaturalShiftedRotation.shifted,
      ``ManuscriptAudit.CubicNaturalShiftedRotation.rotation_some] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
