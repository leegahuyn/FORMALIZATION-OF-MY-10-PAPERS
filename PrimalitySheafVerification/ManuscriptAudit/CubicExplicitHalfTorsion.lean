import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! The actual half of a centered rational two-torsion point from two square roots. -/

namespace ManuscriptAudit.CubicExplicitHalfTorsion

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A a r s : K}

def halfX (a r s : K) : K := a + r * s

def halfY (r s : K) : K := -(r * s) * (r + s)

theorem sum_squared (hSum : r ^ 2 + s ^ 2 = 3 * a) :
    (r + s) ^ 2 = 3 * a + 2 * (r * s) := by
  linear_combination hSum

theorem half_equation (ha : a ^ 3 + A = 0)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2) :
    halfY r s ^ 2 = halfX a r s ^ 3 + A := by
  have hs := sum_squared hSum
  unfold halfY halfX
  linear_combination (r * s) ^ 2 * hs + (r * s) * hProd - ha

/-- The explicitly given affine half on the nonsingular cubic. -/
def halfPoint (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (ha : a ^ 3 + A = 0)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2) :
    (Curve A).Point :=
  Affine.Point.some (halfX a r s) (halfY r s)
    ((nonsingular_iff hΔ _ _).mpr (half_equation ha hSum hProd))

/-- The native point with a root of the cubic as abscissa and zero ordinate. -/
def rootPoint (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (ha : a ^ 3 + A = 0) :
    (Curve A).Point :=
  Affine.Point.some a 0 ((nonsingular_iff hΔ _ _).mpr (by simp [ha]))

theorem negY_eq (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

theorem addX_eq (x z m : K) : (Curve A).addX x z m = m ^ 2 - x - z := by
  simp [Curve, CubicAffine, shortCubic, Affine.addX]

/-- Doubling the explicit half gives the actual point `(a,0)` in the native group law. -/
theorem double_half (h₂ : (2 : K) ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (ha : a ^ 3 + A = 0) (hSum : r ^ 2 + s ^ 2 = 3 * a)
    (hProd : (r * s) ^ 2 = 3 * a ^ 2) (hRS : r * s ≠ 0) (hPlus : r + s ≠ 0) :
    (2 : ℕ) • halfPoint hΔ ha hSum hProd = rootPoint hΔ ha := by
  let W := Curve A
  let x := halfX a r s
  let y := halfY r s
  have hy : y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hRS) hPlus
  have hd : (2 : K) * y ≠ 0 := mul_ne_zero h₂ hy
  have hNeg : y ≠ W.negY x y := by
    rw [show W.negY x y = -y from negY_eq (A := A) x y]
    intro h
    apply hd
    calc
      _ = y + y := two_mul y
      _ = (-y) + y := congrArg (fun u => u + y) h
      _ = 0 := neg_add_cancel y
  have hsq := sum_squared hSum
  let ell := W.slope x x y y
  have hSlope : ell = -(r + s) := by
    change W.slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hNeg, show W.negY x y = -y from negY_eq (A := A) x y,
      sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
    apply (div_eq_iff hd).mpr
    dsimp only [x, y, halfX, halfY]
    linear_combination -2 * (r * s) * hsq - hProd
  have hX : W.addX x x ell = a := by
    rw [show W.addX x x ell = ell ^ 2 - x - x from addX_eq (A := A) x x ell,
      hSlope, neg_sq]
    dsimp only [x, halfX]
    linear_combination hsq
  have hY : W.addY x x y ell = 0 := by
    rw [Affine.addY, Affine.negAddY, hX]
    change (Curve A).negY a (ell * (a - x) + y) = 0
    rw [negY_eq, hSlope]
    dsimp only [x, y, halfX, halfY]
    ring
  unfold halfPoint rootPoint
  rw [two_nsmul, Affine.Point.add_of_Y_ne hNeg, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.CubicExplicitHalfTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicExplicitHalfTorsion.half_equation,
      ``ManuscriptAudit.CubicExplicitHalfTorsion.double_half] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
