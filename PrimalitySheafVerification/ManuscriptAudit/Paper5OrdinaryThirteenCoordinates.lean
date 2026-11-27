import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenSecant

/-! The native characteristic-thirteen endomorphism 3−ρ has its computed secant coordinates. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenCoordinates

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicTriplingCoordinates Paper5OrdinaryThirteenAlgebra Paper5OrdinaryThirteenSecant

noncomputable section

variable (K : Type*) [Field K] [CharP K 13] [DecidableEq K]

abbrev Points := (Curve (1 : K)).Point

theorem discriminant_ne_zero : (shortCubic (0 : K) 1).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero
    (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide)) one_ne_zero

def rotation : AddMonoid.End (Points K) :=
  CubicCubeRotation.rotate 3 rotation_cube (discriminant_ne_zero K)

theorem rotation_some {x y : K} (h : (Curve (1 : K)).Nonsingular x y) :
    ∃ h' : (Curve (1 : K)).Nonsingular (3 * x) y,
      rotation K (Affine.Point.some x y h) = Affine.Point.some (3 * x) y h' :=
  ⟨_, CubicCubeRotation.rotate_some rotation_cube (discriminant_ne_zero K) h⟩

theorem rotation_sq (P : Points K) : rotation K (rotation K P) = -P - rotation K P := by
  have h := CubicRotationQuadratic.rotate_sum_eq_zero
    (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide)) one_ne_zero
    rotation_cube rotation_ne_one (discriminant_ne_zero K) P
  change rotation K (rotation K P) + rotation K P + P = 0 at h
  apply sub_eq_zero.mp
  calc
    _ = rotation K (rotation K P) + rotation K P + P := by abel
    _ = _ := h

set_option maxHeartbeats 1000000 in
/-- On the affine secant domain, the actual endomorphism 3−ρ has coordinates (9x¹³,−y¹³). -/
theorem three_sub_rotation_some {x y : K} (hP : (Curve (1 : K)).Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) (hg : x ^ 3 + 4 ≠ 0) (hq : x ^ 3 + 2 ≠ 0) :
    ∃ h' : (Curve (1 : K)).Nonsingular (9 * x ^ 13) (-(y ^ 13)),
      (3 : ℕ) • (Affine.Point.some x y hP : Points K) - rotation K (Affine.Point.some x y hP) =
        Affine.Point.some (9 * x ^ 13) (-(y ^ 13)) h' := by
  let W := Curve (1 : K)
  let P : Points K := .some x y hP
  have h₂ : (2 : K) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : K) ≠ 0 := numeral_ne_zero 3 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero K) x y).mp hP
  obtain ⟨hT, eT⟩ := triple_some_coordinates h₂ h₃ (discriminant_ne_zero K)
    hy hx hg (tripleX_correct hx hg) hP
  have hTriple : (3 : ℕ) • P = Affine.Point.some (tripleX x) (tripleY x y) hT := eT
  obtain ⟨hR, eR⟩ := rotation_some K hP
  have hN : W.Nonsingular (3 * x) (-y) := by
    exact (nonsingular_iff (discriminant_ne_zero K) _ _).mpr
      (by simpa only [neg_sq] using (nonsingular_iff (discriminant_ne_zero K) _ _).mp hR)
  have eN : -rotation K P = Affine.Point.some (3 * x) (-y) hN := by
    change -rotation K (Affine.Point.some x y hP) = _
    rw [eR, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, negY_eq _ _⟩
  have hxU : 3 * x ≠ tripleX x := abscissas_distinct hx hg hq
  let m := W.slope (3 * x) (tripleX x) (-y) (tripleY x y)
  have hm : m = lastSlope x y := (Affine.slope_of_X_ne hxU).trans (lastSlope_correct hx hy hg hq he)
  have hX : W.addX (3 * x) (tripleX x) m = 9 * x ^ 13 := by
    rw [addX_eq, hm]
    exact last_abscissa hx hg he
  have hY : W.addY (3 * x) (tripleX x) (-y) m = -(y ^ 13) := by
    rw [addY_eq, hX, hm]
    linear_combination last_ordinate hx hg he
  have hQ : W.Nonsingular (W.addX (3 * x) (tripleX x) m)
      (W.addY (3 * x) (tripleX x) (-y) m) :=
    Affine.nonsingular_add hN hT (fun h => hxU h.1)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  change (3 : ℕ) • P - rotation K P = _
  rw [sub_eq_add_neg, add_comm ((3 : ℕ) • P), eN, hTriple, Affine.Point.add_of_X_ne hxU,
    Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.Paper5OrdinaryThirteenCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenCoordinates.rotation_some,
      ``ManuscriptAudit.Paper5OrdinaryThirteenCoordinates.rotation_sq,
      ``ManuscriptAudit.Paper5OrdinaryThirteenCoordinates.three_sub_rotation_some] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
