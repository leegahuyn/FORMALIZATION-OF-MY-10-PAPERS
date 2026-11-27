import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTwistFrobenius

/-! A sixth-root scaling is the native cube rotation, with the sign of the ordinate. -/

namespace ManuscriptAudit.CubicSexticRotation

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicPointScaling CubicCubeRotation CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius

noncomputable section

variable (L : Type*) [Field L] [DecidableEq L]

theorem square_cube {v : L} (hv : v ^ 6 = 1) : (v ^ 2) ^ 3 = 1 := by
  rw [← pow_mul]
  exact hv

theorem cube_sign {v : L} (hv : v ^ 6 = 1) : v ^ 3 = 1 ∨ v ^ 3 = -1 := by
  have h : (v ^ 3 - 1) * (v ^ 3 + 1) = 0 := by
    calc
      _ = v ^ 6 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hv
  rcases mul_eq_zero.mp h with hplus | hminus
  · exact Or.inl (sub_eq_zero.mp hplus)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hminus)

theorem rotate_one (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) :
    rotate (1 : L) (one_pow 3) hΔ = (1 : AddMonoid.End (UnitPoints L)) := by
  apply AddMonoidHom.ext
  intro P
  change rotate (1 : L) (one_pow 3) hΔ P = P
  cases P with
  | zero => exact map_zero _
  | some x y h =>
    rw [rotate_some, Affine.Point.some.injEq]
    simp only [one_mul, and_self]

theorem sextic_eq_rotation {v : L} (hv : v ^ 6 = 1)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) (hs : v ^ 3 = 1) :
    sexticScale L hv hΔ = rotate (v ^ 2) (square_cube L hv) hΔ := by
  apply AddMonoidHom.ext
  intro P
  change sexticScale L hv hΔ P = rotate (v ^ 2) (square_cube L hv) hΔ P
  cases P with
  | zero =>
    change sexticScale L hv hΔ (0 : UnitPoints L) = rotate (v ^ 2) (square_cube L hv) hΔ 0
    simp only [map_zero]
  | some x y h =>
    obtain ⟨h', e⟩ := sexticScale_some L hv hΔ h
    rw [e, rotate_some, Affine.Point.some.injEq, hs, one_mul] <;> simp

theorem sextic_eq_neg_rotation {v : L} (hv : v ^ 6 = 1)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) (hs : v ^ 3 = -1) :
    sexticScale L hv hΔ = -(rotate (v ^ 2) (square_cube L hv) hΔ) := by
  apply AddMonoidHom.ext
  intro P
  change sexticScale L hv hΔ P = -(rotate (v ^ 2) (square_cube L hv) hΔ P)
  cases P with
  | zero =>
    change sexticScale L hv hΔ (0 : UnitPoints L) = -(rotate (v ^ 2) (square_cube L hv) hΔ 0)
    simp only [map_zero, neg_zero]
  | some x y h =>
    obtain ⟨h', e⟩ := sexticScale_some L hv hΔ h
    rw [e, rotate_some, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, by simp [hs, Curve, CubicAffine, shortCubic, Affine.negY]⟩

variable (E : Type*) [Field E] [Fintype E] [Algebra E L]

/-- Over a base with degree-six roots of unity, the twist ratio is the power residue of its coefficient. -/
theorem ratio_eq_power (hD : 6 ∣ Fintype.card E - 1) {A : E} {u : L}
    (hu₀ : u ≠ 0) (hu : u ^ 6 = algebraMap E L A) :
    FiniteField.frobeniusAlgHom E L u / u =
      algebraMap E L (A ^ ((Fintype.card E - 1) / 6)) := by
  have hPos : 0 < Fintype.card E := Fintype.card_pos
  obtain ⟨k, hk⟩ := hD
  have hQ : Fintype.card E = 6 * k + 1 := by omega
  have hK : (Fintype.card E - 1) / 6 = k := by omega
  apply (div_eq_iff hu₀).mpr
  change u ^ Fintype.card E = _
  rw [hK, hQ, pow_add, pow_one, pow_mul, hu, map_pow]

end
end ManuscriptAudit.CubicSexticRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSexticRotation.cube_sign,
      ``ManuscriptAudit.CubicSexticRotation.rotate_one,
      ``ManuscriptAudit.CubicSexticRotation.sextic_eq_rotation,
      ``ManuscriptAudit.CubicSexticRotation.sextic_eq_neg_rotation,
      ``ManuscriptAudit.CubicSexticRotation.ratio_eq_power] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
