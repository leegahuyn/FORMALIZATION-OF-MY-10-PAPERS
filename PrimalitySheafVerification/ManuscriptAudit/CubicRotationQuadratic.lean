import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicCubeRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsion
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! The cube-root rotation on the whole native centered-cubic point group satisfies its cyclotomic equation. -/

namespace ManuscriptAudit.CubicRotationQuadratic

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsion
open CubicThreeTorsionOrdinate CubicCubeRotation TorsionFrobeniusModule

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A z : K}

private theorem cyclotomic_eq (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) :
    z ^ 2 + z + 1 = 0 := by
  have h : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      _ = z ^ 3 - 1 := by ring
      _ = _ := by rw [hz, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hz₁)

/-- The literal horizontal line relation holds throughout the native group. -/
theorem rotate_sum_eq_zero (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (P : (Curve A).Point) :
    rotate z hz hΔ (rotate z hz hΔ P) + rotate z hz hΔ P + P = 0 := by
  cases P with
  | zero => simp
  | some x y hP =>
    let W := Curve A
    let r := rotate z hz hΔ
    let P : W.Point := .some x y hP
    change r (r P) + r P + P = 0
    by_cases hx : x = 0
    · have hfix : r P = P := by
        change rotate z hz hΔ (Affine.Point.some x y hP) = Affine.Point.some x y hP
        rw [rotate_some, Affine.Point.some.injEq]
        exact ⟨by rw [hx, mul_zero], rfl⟩
      have hy : y ≠ 0 := by
        intro he
        exact hA (by simpa [hx, he] using ((nonsingular_iff hΔ x y).mp hP).symm)
      have h3p : (3 : ℕ) • P = 0 :=
        (three_nsmul_affine_some_iff h₂ h₃ hΔ hP).mpr ⟨hy, by simp [hx]⟩
      rw [hfix, hfix]
      simpa only [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, two_nsmul, one_nsmul] using h3p
    · have hne : x ≠ z * x := by
        intro he
        have hprod : (z - 1) * x = 0 := by
          rw [sub_mul, one_mul, ← he, sub_self]
        exact mul_ne_zero (sub_ne_zero.mpr hz₁) hx hprod
      let l := W.slope x (z * x) y y
      have hl : l = 0 := by
        change W.slope x (z * x) y y = _
        rw [Affine.slope_of_X_ne hne, sub_self, zero_div]
      have hX : W.addX x (z * x) l = z * (z * x) := by
        simp [hl, W, Curve, CubicAffine, shortCubic, Affine.addX]
        linear_combination -x * cyclotomic_eq hz hz₁
      have hY : W.addY x (z * x) y l = W.negY (z * (z * x)) y := by
        simp [hl, W, Curve, CubicAffine, shortCubic, Affine.addY, Affine.negAddY, Affine.negY]
      have hp : P + r P = - r (r P) := by
        change Affine.Point.some x y hP + rotate z hz hΔ (Affine.Point.some x y hP) =
          -rotate z hz hΔ (rotate z hz hΔ (Affine.Point.some x y hP))
        simp only [rotate_some]
        rw [Affine.Point.add_of_X_ne hne, Affine.Point.neg_some, Affine.Point.some.injEq]
        exact ⟨hX, hY⟩
      calc
        _ = r (r P) + (P + r P) := by abel
        _ = _ := by rw [hp, add_neg_cancel]

theorem rotation_linear_quad (m : ℕ) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (P : Torsion m (Curve A).Point) :
    let S := mapLinear m (rotate z hz hΔ)
    S (S P) + S P + P = 0 := by
  dsimp only
  apply Subtype.ext
  exact rotate_sum_eq_zero h₂ h₃ hA hz hz₁ hΔ P.val

end
end ManuscriptAudit.CubicRotationQuadratic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationQuadratic.rotate_sum_eq_zero,
      ``ManuscriptAudit.CubicRotationQuadratic.rotation_linear_quad] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
