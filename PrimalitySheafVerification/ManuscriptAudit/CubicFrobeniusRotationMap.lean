import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace

/-! Naturality of the actual cubic coordinate rotation under field maps. -/

namespace ManuscriptAudit.CubicFrobeniusRotationMap

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicCubeRotation
open CubicNonsplitFrobeniusTrace

noncomputable section

variable (E : Type*) [Field E]
variable (L : Type*) [Field L] [Algebra E L] [DecidableEq L]

/-- A field endomorphism carries a coordinate rotation to the image rotation. -/
theorem pointMapAt_intertwines_rotation (W : Affine E) {a z w : L}
    (hW : W.baseChange L = Curve a) (g : L →ₐ[E] L) (hgz : g z = w)
    (hz : z ^ 3 = 1) (hw : w ^ 3 = 1)
    (hΔ : (shortCubic (0 : L) a).Δ ≠ 0)
    (P : (Curve a).Point) :
    let f := pointMapAt E L W (Curve a) hW g
    f (rotate z hz hΔ P) = rotate w hw hΔ (f P) := by
  let f := pointMapAt E L W (Curve a) hW g
  change f (rotate z hz hΔ P) = rotate w hw hΔ (f P)
  cases P with
  | zero =>
    change f (rotate z hz hΔ 0) = rotate w hw hΔ (f 0)
    simp only [map_zero]
  | some x y h =>
    have hR : (Curve a).Nonsingular (z * x) y := by
      apply (nonsingular_iff hΔ _ _).mpr
      rw [mul_pow, hz, one_mul]
      exact (nonsingular_iff hΔ _ _).mp h
    have eR : rotate z hz hΔ (Affine.Point.some x y h) =
        Affine.Point.some (z * x) y hR := rotate_some hz hΔ h
    obtain ⟨h₁, e₁⟩ := pointMapAt_some E L W (Curve a) hW g (z * x) y hR
    obtain ⟨h₂, e₂⟩ := pointMapAt_some E L W (Curve a) hW g x y h
    change f (Affine.Point.some (z * x) y hR) = _ at e₁
    change f (Affine.Point.some x y h) = _ at e₂
    rw [eR, e₁, e₂, rotate_some, Affine.Point.some.injEq]
    exact ⟨by rw [map_mul, hgz], rfl⟩

end
end ManuscriptAudit.CubicFrobeniusRotationMap

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicFrobeniusRotationMap.pointMapAt_intertwines_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
