import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenGeometry
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenSecant

/-! The actual characteristic-seven endomorphism 2−ρ has seventh-power coordinates. -/

namespace ManuscriptAudit.Paper5OrdinarySevenFrobeniusCoordinates

open WeierstrassCurve Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenSecant

noncomputable section

variable (F : Type*) [Field F] [CharP F 7] [DecidableEq F]

private abbrev W := (ordinaryCurve F).toAffine

set_option maxHeartbeats 1200000 in
private theorem double_point {x y : F} (hP : (W F).Nonsingular x y) (hy : y ≠ 0) :
    ∃ hQ : (W F).Nonsingular (doubleX x y) (doubleY x y),
      (2 : ℕ) • (Affine.Point.some x y hP : (W F).Point) = Affine.Point.some (doubleX x y) (doubleY x y) hQ := by
  have hy' : y ≠ -y := by
    intro h
    exact (mul_ne_zero two_ne hy) (by linear_combination h)
  have hyN : y ≠ (W F).negY x y := by simpa only [negY_eq] using hy'
  let s := (W F).slope x x y y
  have hs : s = tangent x y := tangent_slope F x y hy'
  have hX : (W F).addX x x s = doubleX x y := by
    rw [addX_eq, hs]
    rfl
  have hY : (W F).addY x x y s = doubleY x y := by
    rw [addY_eq, hX, hs]
    rfl
  have hQ : (W F).Nonsingular ((W F).addX x x s) ((W F).addY x x y s) :=
    Affine.nonsingular_add hP hP (fun h => hyN h.2)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hyN, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

set_option maxHeartbeats 1200000 in
private theorem two_sub_regular {x y : F} (hP : (W F).Nonsingular x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ hQ : (W F).Nonsingular (4 * x ^ 7) (-(y ^ 7)),
      (2 : ℕ) • (Affine.Point.some x y hP : (W F).Point) - rotation F (Affine.Point.some x y hP) =
        Affine.Point.some (4 * x ^ 7) (-(y ^ 7)) hQ := by
  let P : (W F).Point := .some x y hP
  have he := (equation_iff F x y).mp hP.1
  obtain ⟨hd, eD⟩ := double_point F hP hy
  have hNeg : (W F).Nonsingular (2 * x) (-y) := by
    simpa only [negY_eq] using
      (Affine.nonsingular_neg (W' := W F) (2 * x) y).mpr (scaledNonsingular F x y hP)
  have eN : -rotation F P = Affine.Point.some (2 * x) (-y) hNeg := by
    change -rotation F (Affine.Point.some x y hP) = _
    rw [rotation_some, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, negY_eq F _ _⟩
  have hxD : 2 * x ≠ doubleX x y := abscissas_ne hx hy he
  let s := (W F).slope (2 * x) (doubleX x y) (-y) (doubleY x y)
  have hs : s = chord x y := (Affine.slope_of_X_ne hxD).trans (actual_chord hx hy he)
  have hX : (W F).addX (2 * x) (doubleX x y) s = 4 * x ^ 7 := by
    rw [addX_eq, hs]
    exact chord_abscissa hy he
  have hY : (W F).addY (2 * x) (doubleX x y) (-y) s = -(y ^ 7) := by
    rw [addY_eq, hX, hs]
    exact chord_ordinate hy he
  have hQ : (W F).Nonsingular ((W F).addX (2 * x) (doubleX x y) s)
      ((W F).addY (2 * x) (doubleX x y) (-y) s) :=
    Affine.nonsingular_add hNeg hd (fun h => hxD h.1)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  change (2 : ℕ) • P - rotation F P = _
  rw [sub_eq_add_neg, add_comm ((2 : ℕ) • P), eN, eD, Affine.Point.add_of_X_ne hxD,
    Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

set_option maxHeartbeats 1200000 in
/-- At every finite point, the endomorphism 2−ρ has coordinates (4x⁷,−y⁷). -/
theorem two_sub_rotation_coordinates {x y : F} (hP : (W F).Nonsingular x y) :
    ∃ hQ : (W F).Nonsingular (4 * x ^ 7) (-(y ^ 7)),
      (2 : ℕ) • (Affine.Point.some x y hP : (W F).Point) - rotation F (Affine.Point.some x y hP) =
        Affine.Point.some (4 * x ^ 7) (-(y ^ 7)) hQ := by
  have h7 := seven_zero F
  by_cases hx : x = 0
  · subst x
    have he : y ^ 2 = 5 := by simpa using (equation_iff F 0 y).mp hP.1
    have hY : -(y ^ 7) = y := by
      calc
        _ = -(y * (y ^ 2) ^ 3) := by ring
        _ = _ := by rw [he]; linear_combination (-18 * y) * h7
    let P : (W F).Point := .some 0 y hP
    have hR : rotation F P = P := by
      change rotation F (Affine.Point.some 0 y hP) = Affine.Point.some 0 y hP
      rw [rotation_some, Affine.Point.some.injEq]
      simp
    refine ⟨by simpa only [zero_pow (by decide : (7 : ℕ) ≠ 0), mul_zero, hY] using hP, ?_⟩
    change (2 : ℕ) • P - rotation F P = _
    rw [hR, two_nsmul, add_sub_cancel_right]
    change Affine.Point.some 0 y hP = _
    rw [Affine.Point.some.injEq]
    simp [hY]
  by_cases hy : y = 0
  · subst y
    have he : (0 : F) = x ^ 3 + 5 := by simpa using (equation_iff F x 0).mp hP.1
    have hX3 : x ^ 3 = 2 := by linear_combination -he - h7
    have hX : 4 * x ^ 7 = 2 * x := by
      calc
        _ = 4 * x * (x ^ 3) ^ 2 := by ring
        _ = _ := by rw [hX3]; linear_combination (2 * x) * h7
    have hyNeg : (0 : F) = (W F).negY x 0 := by rw [negY_eq, neg_zero]
    have hTwo : (2 : ℕ) • (Affine.Point.some x 0 hP : (W F).Point) = 0 := by
      rw [two_nsmul, Affine.Point.add_self_of_Y_eq hyNeg]
    refine ⟨by simpa only [hX, zero_pow (by decide : (7 : ℕ) ≠ 0), neg_zero] using
      scaledNonsingular F x 0 hP, ?_⟩
    rw [hTwo, zero_sub, rotation_some, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨hX.symm, by simp [ordinaryCurve]⟩
  exact two_sub_regular F hP hx hy

end
end ManuscriptAudit.Paper5OrdinarySevenFrobeniusCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySevenFrobeniusCoordinates.two_sub_rotation_coordinates
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
