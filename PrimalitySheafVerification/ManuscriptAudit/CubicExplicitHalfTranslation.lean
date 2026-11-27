import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicExplicitHalfTorsion

/-! Sign changes in the explicit half are actual translations by two-torsion. -/

namespace ManuscriptAudit.CubicExplicitHalfTranslation

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicExplicitHalfTorsion

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A a b r s : K}

theorem half_comm (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (ha : a ^ 3 + A = 0)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2) :
    halfPoint hΔ ha hSum hProd =
      halfPoint (r := s) (s := r) hΔ ha
        (by simpa only [add_comm] using hSum) (by simpa only [mul_comm] using hProd) := by
  unfold halfPoint
  rw [Affine.Point.some.injEq]
  exact ⟨by simp only [halfX, mul_comm], by simp only [halfY, mul_comm, add_comm]⟩

/-- Flipping the second square root translates the half by the point at the other root
from which the first square root was obtained. -/
theorem add_root_eq_flip_s (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (ha : a ^ 3 + A = 0) (hb : b ^ 3 + A = 0)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2)
    (hrb : r ^ 2 = a - b) (hr : r ≠ 0) (hPlus : r + s ≠ 0) :
    halfPoint hΔ ha hSum hProd + rootPoint hΔ hb =
      halfPoint (r := r) (s := -s) hΔ ha (by simpa [neg_sq] using hSum)
        (by simpa [mul_neg, neg_sq] using hProd) := by
  let W := Curve A
  let x := halfX a r s
  let y := halfY r s
  let x' := halfX a r (-s)
  let y' := halfY r (-s)
  have hden : x - b = r * (r + s) := by
    dsimp only [x, halfX]
    linear_combination -hrb
  have hd : x - b ≠ 0 := by rw [hden]; exact mul_ne_zero hr hPlus
  have hxb : x ≠ b := sub_ne_zero.mp hd
  let ell := W.slope x b y 0
  have hSlope : ell = -s := by
    change W.slope x b y 0 = _
    rw [Affine.slope_of_X_ne hxb, sub_zero]
    apply (div_eq_iff hd).mpr
    rw [hden]
    dsimp only [y, halfY]
    ring
  have hX : W.addX x b ell = x' := by
    rw [show W.addX x b ell = ell ^ 2 - x - b from addX_eq (A := A) x b ell,
      hSlope, neg_sq]
    dsimp only [x, x', halfX]
    linear_combination hSum - hrb
  have hY : W.addY x b y ell = y' := by
    rw [Affine.addY, Affine.negAddY, hX]
    change (Curve A).negY x' (ell * (x' - x) + y) = y'
    rw [negY_eq, hSlope]
    dsimp only [x, y, x', y', halfX, halfY]
    ring
  unfold halfPoint rootPoint
  rw [Affine.Point.add_of_X_ne hxb, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

/-- The corresponding translation for the first square root. -/
theorem add_root_eq_flip_r (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (ha : a ^ 3 + A = 0) (hb : b ^ 3 + A = 0)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2)
    (hsb : s ^ 2 = a - b) (hs : s ≠ 0) (hPlus : r + s ≠ 0) :
    halfPoint hΔ ha hSum hProd + rootPoint hΔ hb =
      halfPoint (r := -r) (s := s) hΔ ha (by simpa [neg_sq] using hSum)
        (by simpa [neg_mul, neg_sq] using hProd) := by
  have hSum' : s ^ 2 + r ^ 2 = 3 * a := by simpa only [add_comm] using hSum
  have hProd' : (s * r) ^ 2 = 3 * a ^ 2 := by simpa only [mul_comm] using hProd
  have hPlus' : s + r ≠ 0 := by simpa only [add_comm] using hPlus
  rw [half_comm hΔ ha hSum hProd]
  exact (add_root_eq_flip_s hΔ ha hb hSum' hProd' hsb hs hPlus').trans
    (half_comm (r := s) (s := -r) hΔ ha
      (by simpa [neg_sq] using hSum') (by simpa [mul_neg, neg_sq] using hProd'))

end
end ManuscriptAudit.CubicExplicitHalfTranslation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicExplicitHalfTranslation.add_root_eq_flip_s,
      ``ManuscriptAudit.CubicExplicitHalfTranslation.add_root_eq_flip_r] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
