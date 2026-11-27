import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenSecant

/-! The actual characteristic-nineteen group law computes 3−2ρ² on a cofinite domain. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenCoordinates

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicTriplingCoordinates Paper5OrdinaryNineteenAlgebra Paper5OrdinaryNineteenSecant

noncomputable section

variable (K : Type*) [Field K] [CharP K 19] [DecidableEq K]

abbrev Points := (Curve (1 : K)).Point

theorem discriminant_ne_zero : (shortCubic (0 : K) 1).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero
    (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide)) one_ne_zero

def rotation : AddMonoid.End (Points K) :=
  CubicCubeRotation.rotate 7 rotation_cube (discriminant_ne_zero K)

theorem rotation_some {x y : K} (h : (Curve (1 : K)).Nonsingular x y) :
    ∃ h' : (Curve (1 : K)).Nonsingular (7 * x) y,
      rotation K (Affine.Point.some x y h) = Affine.Point.some (7 * x) y h' :=
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

private def unrotatedDoubleX (x : K) : K := x * ((x ^ 3 - 8) / doubleDenominator (x ^ 3))

private def positiveDoubleY (x y : K) : K :=
  y * (doubleOrdinateNumerator (x ^ 3) / doubleOrdinateDenominator (x ^ 3))

set_option maxHeartbeats 700000 in
private theorem double_some {x y : K} (hP : (Curve (1 : K)).Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : (Curve (1 : K)).Nonsingular (unrotatedDoubleX K x) (positiveDoubleY K x y),
      (2 : ℕ) • (Affine.Point.some x y hP : Points K) =
        Affine.Point.some (unrotatedDoubleX K x) (positiveDoubleY K x y) h' := by
  let W := Curve (1 : K)
  have h₂ : (2 : K) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₄ : (4 : K) ≠ 0 := numeral_ne_zero 4 (by decide)
  have h₈ : (8 : K) ≠ 0 := numeral_ne_zero 8 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero K) x y).mp hP
  have hs : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  have hyN : y ≠ W.negY x y := by
    change y ≠ (Curve (1 : K)).negY x y
    rw [negY_eq]
    intro he'
    exact (mul_ne_zero h₂ hy) (by linear_combination he')
  let ell := W.slope x x y y
  have hEll : ell = 3 * x ^ 2 / (2 * y) := by
    change W.slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hyN, negY_eq, sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
  have hEll' : ell = (3 * x ^ 2 * y) / (2 * (x ^ 3 + 1)) := by
    rw [hEll, ← he]
    field_simp [h₂, hy] <;> ring
  have hX : W.addX x x ell = unrotatedDoubleX K x := by
    rw [addX_eq, hEll]
    simp only [div_pow, mul_pow, he]
    unfold unrotatedDoubleX doubleDenominator
    field_simp [h₄, h₂, hs] <;> ring
  have hY : W.addY x x y ell = positiveDoubleY K x y := by
    rw [addY_eq, hX, hEll']
    unfold unrotatedDoubleX positiveDoubleY doubleDenominator doubleOrdinateDenominator
    rw [← double_ordinate_numerator_eq]
    field_simp [h₄, h₈, h₂, hs] <;> ring
  have hQ : W.Nonsingular (W.addX x x ell) (W.addY x x y ell) :=
    Affine.nonsingular_add hP hP (fun h => hyN h.2)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  rw [two_nsmul, Affine.Point.add_of_Y_ne hyN, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

private theorem rotated_double_abscissa (x : K) :
    (7 : K) * (7 * unrotatedDoubleX K x) = doubleX x := by
  unfold unrotatedDoubleX doubleX
  calc
    _ = x * (((7 : K) ^ 2 * (x ^ 3 - 8)) / doubleDenominator (x ^ 3)) := by ring
    _ = _ := by rw [rotation_square, rotated_double_numerator_eq]

set_option maxHeartbeats 700000 in
theorem minus_rotated_double_some {x y : K} (hP : (Curve (1 : K)).Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : (Curve (1 : K)).Nonsingular (doubleX x) (minusDoubleY x y),
      -((2 : ℕ) • rotation K (rotation K (Affine.Point.some x y hP))) =
        Affine.Point.some (doubleX x) (minusDoubleY x y) h' := by
  obtain ⟨hD, eD⟩ := double_some K hP hy
  obtain ⟨hR, eR⟩ := rotation_some K hD
  obtain ⟨hR', eR'⟩ := rotation_some K hR
  let xn := 7 * (7 * unrotatedDoubleX K x)
  let yn := positiveDoubleY K x y
  have eX : xn = doubleX x := rotated_double_abscissa K x
  have eY : (Curve (1 : K)).negY xn yn = minusDoubleY x y := by
    rw [negY_eq]
    unfold yn positiveDoubleY minusDoubleY
    ring
  have hN : (Curve (1 : K)).Nonsingular xn ((Curve (1 : K)).negY xn yn) :=
    (Affine.nonsingular_neg ..).mpr hR'
  refine ⟨by simpa only [← eX, ← eY] using hN, ?_⟩
  let P : Points K := Affine.Point.some x y hP
  have hScale : (2 : ℕ) • rotation K (rotation K P) = rotation K (rotation K ((2 : ℕ) • P)) := by
    rw [map_nsmul, map_nsmul]
  change -((2 : ℕ) • rotation K (rotation K P)) = _
  rw [hScale]
  change -rotation K (rotation K ((2 : ℕ) • (Affine.Point.some x y hP : Points K))) = _
  rw [eD, eR, eR', Affine.Point.neg_some, Affine.Point.some.injEq]
  exact ⟨eX, eY⟩

set_option maxHeartbeats 900000 in
/-- The computed Frobenius coordinates are those of the actual endomorphism 3−2ρ². -/
theorem three_sub_two_rotation_sq_some {x y : K} (hP : (Curve (1 : K)).Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) (hg : x ^ 3 + 4 ≠ 0) (h1 : x ^ 3 ≠ 1) :
    ∃ h' : (Curve (1 : K)).Nonsingular (x ^ 19) (y ^ 19),
      (3 : ℕ) • (Affine.Point.some x y hP : Points K) -
        (2 : ℕ) • rotation K (rotation K (Affine.Point.some x y hP)) =
          Affine.Point.some (x ^ 19) (y ^ 19) h' := by
  let W := Curve (1 : K)
  let P : Points K := .some x y hP
  have h₂ : (2 : K) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : K) ≠ 0 := numeral_ne_zero 3 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero K) x y).mp hP
  have hs : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  obtain ⟨hT, eT⟩ := triple_some_coordinates h₂ h₃ (discriminant_ne_zero K)
    hy hx (by simpa only [mul_one] using hg) (tripleX_correct hx hg) hP
  have hY' := tripleY_correct hx hy hg he
  have hT' : W.Nonsingular (tripleX x) (tripleY x y) := by
    simpa only [hY'] using hT
  have hTriple : (3 : ℕ) • P = Affine.Point.some (tripleX x) (tripleY x y) hT' := by
    refine eT.trans ?_
    rw [Affine.Point.some.injEq]
    exact ⟨rfl, hY'⟩
  obtain ⟨hN, eN⟩ := minus_rotated_double_some K hP hy
  have hxU : doubleX x ≠ tripleX x := abscissas_distinct hx hs hg h1
  let m := W.slope (doubleX x) (tripleX x) (minusDoubleY x y) (tripleY x y)
  have hm : m = lastSlope x y := (Affine.slope_of_X_ne hxU).trans (lastSlope_correct hx hs hg h1)
  have hX : W.addX (doubleX x) (tripleX x) m = x ^ 19 := by
    rw [addX_eq, hm]
    exact last_abscissa hx hg he hs
  have hY : W.addY (doubleX x) (tripleX x) (minusDoubleY x y) m = y ^ 19 := by
    rw [addY_eq, hX, hm]
    exact last_ordinate hx hg he hs
  have hQ : W.Nonsingular (W.addX (doubleX x) (tripleX x) m)
      (W.addY (doubleX x) (tripleX x) (minusDoubleY x y) m) :=
    Affine.nonsingular_add hN hT' (fun h => hxU h.1)
  have hAdd : Affine.Point.some (doubleX x) (minusDoubleY x y) hN +
      Affine.Point.some (tripleX x) (tripleY x y) hT' =
      Affine.Point.some (W.addX (doubleX x) (tripleX x) m)
        (W.addY (doubleX x) (tripleX x) (minusDoubleY x y) m) hQ :=
    Affine.Point.add_of_X_ne (h₁ := hN) (h₂ := hT') hxU
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  change (3 : ℕ) • P - (2 : ℕ) • rotation K (rotation K (Affine.Point.some x y hP)) = _
  rw [sub_eq_add_neg, add_comm ((3 : ℕ) • P), eN, hTriple, hAdd, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.Paper5OrdinaryNineteenCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenCoordinates.rotation_some,
      ``ManuscriptAudit.Paper5OrdinaryNineteenCoordinates.rotation_sq,
      ``ManuscriptAudit.Paper5OrdinaryNineteenCoordinates.minus_rotated_double_some,
      ``ManuscriptAudit.Paper5OrdinaryNineteenCoordinates.three_sub_two_rotation_sq_some] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
