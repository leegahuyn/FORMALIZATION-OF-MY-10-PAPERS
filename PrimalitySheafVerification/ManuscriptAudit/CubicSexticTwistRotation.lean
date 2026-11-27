import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.End
import PrimalitySheafVerification.ManuscriptAudit.CubicPointScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicCubeRotation

/-! Identify the actual sixth-root scaling as a signed cube rotation. -/

namespace ManuscriptAudit.CubicSexticTwistRotation

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicPointScaling CubicCubeRotation

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A u v : K}

private theorem negY_eq (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

/-- On the actual point group, a sixth-root scale uses its square on abscissas
and the integer sign of its cube on ordinates. -/
theorem scale_eq_signed_rotate (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (hv : v ≠ 0) (hV : v ^ 6 * A = A) (hu₃ : u ^ 3 = 1) (hu : v ^ 2 = u)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hSign : v ^ 3 = (ε : K)) :
    scale hv hV hΔ = ε • rotate u hu₃ hΔ := by
  rcases hε with h | h
  · subst ε
    rw [one_zsmul]
    apply AddMonoidHom.ext
    intro P
    cases P with
    | zero =>
        change scale hv hV hΔ (0 : (Curve A).Point) = rotate u hu₃ hΔ 0
        rw [map_zero, map_zero]
    | some x y hP =>
        rw [scale_some, rotate_some, Affine.Point.some.injEq]
        exact ⟨by rw [hu], by rw [hSign, Int.cast_one, one_mul]⟩
  · subst ε
    rw [neg_one_zsmul]
    apply AddMonoidHom.ext
    intro P
    change scale hv hV hΔ P = -rotate u hu₃ hΔ P
    cases P with
    | zero =>
        change scale hv hV hΔ (0 : (Curve A).Point) = -rotate u hu₃ hΔ 0
        rw [map_zero, map_zero, neg_zero]
    | some x y hP =>
        rw [scale_some, rotate_some, Affine.Point.neg_some, Affine.Point.some.injEq]
        exact ⟨by rw [hu], by rw [hSign, Int.cast_neg, Int.cast_one, neg_one_mul, negY_eq]⟩

/-- Squaring the actual rotation acts by the square of its scalar on abscissas. -/
theorem rotate_square_eq (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (hu₃ : u ^ 3 = 1) (hu₂₃ : (u ^ 2) ^ 3 = 1) :
    rotate (u ^ 2) hu₂₃ hΔ = (rotate u hu₃ hΔ).comp (rotate u hu₃ hΔ) := by
  apply AddMonoidHom.ext
  intro P
  change rotate (u ^ 2) hu₂₃ hΔ P = rotate u hu₃ hΔ (rotate u hu₃ hΔ P)
  cases P with
  | zero =>
      change rotate (u ^ 2) hu₂₃ hΔ (0 : (Curve A).Point) =
        rotate u hu₃ hΔ (rotate u hu₃ hΔ 0)
      simp only [map_zero]
  | some x y hP =>
      simp only [rotate_some, Affine.Point.some.injEq]
      exact ⟨by ring, rfl⟩

end
end ManuscriptAudit.CubicSexticTwistRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSexticTwistRotation.scale_eq_signed_rotate,
      ``ManuscriptAudit.CubicSexticTwistRotation.rotate_square_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
