import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeAdicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenFrobenius

/-! The native thirteen-torsion of the ordinary centered cubic is the conjugate Frobenius kernel. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel

open WeierstrassCurve CubicThreeTorsionOrdinate Paper5OrdinaryThirteenAlgebra
open Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenFrobenius

noncomputable section

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]

private theorem rotation_cube_apply (P : Points L) :
    rotation L (rotation L (rotation L P)) = P :=
  CubicCubeRotation.rotate_cube rotation_cube (discriminant_ne_zero L) P

private theorem rotation_injective : Function.Injective (rotation L) := by
  intro P Q he
  have h := congrArg (fun R : Points L => rotation L (rotation L R)) he
  simpa only [rotation_cube_apply] using h

theorem frobenius_injective : Function.Injective (nativeFrobenius L) :=
  CubicThreeAdicFrobenius.pointMapAt_injective (ZMod 13) L
    (Curve (1 : ZMod 13)) (Curve (1 : L)) (ordinary_baseChange L)
    (FiniteField.frobeniusAlgHom (ZMod 13) L)

/-- The ordinary conjugate of the actual Frobenius in the native rotation ring. -/
def conjugateFrobenius : AddMonoid.End (Points L) :=
  -(1 : AddMonoid.End (Points L)) - (4 : ℕ) • rotation L ^ 2

theorem frobenius_mul_conjugate_apply (P : Points L) :
    nativeFrobenius L (conjugateFrobenius L P) = (13 : ℕ) • P := by
  have hF (Q : Points L) : nativeFrobenius L Q = -Q - (4 : ℕ) • rotation L Q :=
    congrArg (fun f : AddMonoid.End (Points L) => f Q) (native_eq_rotation L)
  have hV : conjugateFrobenius L P = -P - (4 : ℕ) • rotation L (rotation L P) := rfl
  rw [hF, hV, map_sub, map_neg, map_nsmul, rotation_cube_apply, rotation_sq]
  abel

theorem conjugate_factor_apply (P : Points L) :
    conjugateFrobenius L P = -rotation L (rotation L ((3 : ℕ) • P - rotation L (rotation L P))) := by
  change -P - (4 : ℕ) • rotation L (rotation L P) = _
  have hFour : rotation L (rotation L (rotation L (rotation L P))) = rotation L P := by
    rw [rotation_cube_apply]
  simp only [map_sub, map_nsmul, hFour]
  rw [rotation_sq]
  abel

/-- The thirteen-torsion condition is the elementary equality [3]P=ρ²P. -/
theorem torsion_iff (P : Points L) :
    (13 : ℕ) • P = 0 ↔ (3 : ℕ) • P = rotation L (rotation L P) := by
  constructor
  · intro hp
    have h : nativeFrobenius L (conjugateFrobenius L P) = nativeFrobenius L 0 := by
      rw [frobenius_mul_conjugate_apply, hp, map_zero]
    have hz := frobenius_injective L h
    rw [conjugate_factor_apply] at hz
    have hh := neg_eq_zero.mp hz
    have he : rotation L (rotation L ((3 : ℕ) • P - rotation L (rotation L P))) =
        rotation L (rotation L 0) := by simpa only [map_zero] using hh
    exact sub_eq_zero.mp (rotation_injective L (rotation_injective L he))
  · intro hp
    rw [← frobenius_mul_conjugate_apply, conjugate_factor_apply, hp, sub_self]
    simp only [map_zero, neg_zero]

end
end ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel.frobenius_injective,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel.frobenius_mul_conjugate_apply,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel.conjugate_factor_apply,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel.torsion_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
