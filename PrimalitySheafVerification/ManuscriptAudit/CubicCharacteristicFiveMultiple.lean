import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacteristicFiveSecant
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsion

/-! The native fifth multiple of every affine point on the characteristic-five centered cubic. -/

namespace ManuscriptAudit.CubicCharacteristicFiveMultiple

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsion
open CubicThreeTorsionOrdinate CubicCharacteristicFiveIdentities CubicCharacteristicFiveDouble
open CubicCharacteristicFiveSecant

noncomputable section

private theorem five_nsmul_self_of_four {G : Type*} [AddCommGroup G] {P : G}
    (h : (4 : ℕ) • P = 0) : (5 : ℕ) • P = P := by
  rw [show (5 : ℕ) = 4 + 1 by decide, add_nsmul, h, one_nsmul, zero_add]

private theorem five_nsmul_neg_of_three {G : Type*} [AddCommGroup G] {P : G}
    (h : (3 : ℕ) • P = 0) : (5 : ℕ) • P = -P := by
  have h₆ : (6 : ℕ) • P = 0 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, mul_nsmul, h, smul_zero]
  apply eq_neg_of_add_eq_zero_left
  calc
    _ = (5 : ℕ) • P + (1 : ℕ) • P := by rw [one_nsmul]
    _ = 0 := by rw [← add_nsmul]; exact h₆

variable {K : Type*} [Field K] [CharP K 5] [DecidableEq K] {A : K}

private theorem fourth_torsion_powers {t : K} (ht : ordinateFactor t = 0) :
    t ^ 8 = 1 ∧ (t + 1) ^ 12 = -1 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2 : t ^ 2 = 3 := by
    unfold ordinateFactor at ht
    linear_combination 3 * ht - t ^ 2 * h5
  have h9 : (3 : K) ^ 2 = -1 := by linear_combination 2 * h5
  have h4 : t ^ 4 = -1 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, h2, h9]
  have hbin : (t + 1) ^ 5 = t ^ 5 + 1 := by
    linear_combination (t ^ 4 + 2 * t ^ 3 + 2 * t ^ 2 + t) * h5
  have h6 : (t + 1) ^ 6 = 3 := by
    calc
      _ = (t + 1) ^ 5 * (t + 1) := by ring
      _ = 1 - t ^ 2 := by
        rw [hbin, show t ^ 5 = t ^ 4 * t by ring, h4]
        ring
      _ = 3 := by rw [h2]; linear_combination -h5
  constructor
  · rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, h4]
    ring
  · rw [show (12 : ℕ) = 6 * 2 by decide, pow_mul, h6, h9]

set_option maxHeartbeats 750000 in
theorem five_some {x y : K} (hA : A ≠ 0) (hA4 : A ^ 4 = 1)
    (hP : (Curve A).Nonsingular x y) :
    ∃ h : (Curve A).Nonsingular (x ^ 25) (-(y ^ 25)),
      (5 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) =
        Affine.Point.some (x ^ 25) (-(y ^ 25)) h := by
  let W := Curve A
  let P : W.Point := .some x y hP
  let hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero two_ne three_ne hA
  let t := x ^ 3 / A
  have hCube : x ^ 3 = A * t := by
    dsimp only [t]
    field_simp [hA] <;> ring
  have hySq : y ^ 2 = A * (t + 1) := by
    rw [(nonsingular_iff hΔ x y).mp hP, hCube]
    ring
  have hA8 : A ^ 8 = 1 := by rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, hA4, one_pow]
  have hA12 : A ^ 12 = 1 := by rw [show (12 : ℕ) = 4 * 3 by decide, pow_mul, hA4, one_pow]
  have hx25 : x ^ 25 = x * t ^ 8 := by
    calc
      _ = x * (x ^ 3) ^ 8 := by ring
      _ = _ := by rw [hCube, mul_pow, hA8, one_mul]
  have hy25 : y ^ 25 = y * (t + 1) ^ 12 := by
    calc
      _ = y * (y ^ 2) ^ 12 := by ring
      _ = _ := by rw [hySq, mul_pow, hA12, one_mul]
  have self_case (h₄ : (4 : ℕ) • P = 0) (hX : x ^ 25 = x) (hY : -(y ^ 25) = y) :
      ∃ h : W.Nonsingular (x ^ 25) (-(y ^ 25)),
        (5 : ℕ) • P = Affine.Point.some (x ^ 25) (-(y ^ 25)) h := by
    have h : W.Nonsingular (x ^ 25) (-(y ^ 25)) := by rw [hX, hY]; exact hP
    refine ⟨h, (five_nsmul_self_of_four h₄).trans ?_⟩
    change Affine.Point.some x y hP = _
    rw [Affine.Point.some.injEq]
    exact ⟨hX.symm, hY.symm⟩
  have flex_case (hy : y ≠ 0) (hf : x * (x ^ 3 + 4 * A) = 0)
      (hX : x ^ 25 = x) (hY : y ^ 25 = y) :
      ∃ h : W.Nonsingular (x ^ 25) (-(y ^ 25)),
        (5 : ℕ) • P = Affine.Point.some (x ^ 25) (-(y ^ 25)) h := by
    have h₃ := (three_nsmul_affine_some_iff two_ne three_ne hΔ hP).mpr ⟨hy, hf⟩
    have hn : W.Nonsingular x (W.negY x y) := (Affine.nonsingular_neg (W' := W) x y).mpr hP
    have h : W.Nonsingular (x ^ 25) (-(y ^ 25)) := by
      rw [hX, hY, ← negY (A := A) x y]
      exact hn
    refine ⟨h, (five_nsmul_neg_of_three h₃).trans ?_⟩
    change -(Affine.Point.some x y hP : W.Point) = _
    rw [Affine.Point.neg_some, Affine.Point.some.injEq, negY]
    exact ⟨hX.symm, congrArg Neg.neg hY.symm⟩
  by_cases hy : y = 0
  · have h₂ := (two_nsmul_affine_some_iff two_ne hP).mpr hy
    have h₄ : (4 : ℕ) • P = 0 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul]
      change 2 • (2 • Affine.Point.some x y hP) = _
      rw [h₂, smul_zero]
    have ht : t = -1 := by
      have d := hySq
      rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)] at d
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp d.symm).resolve_left hA)
    apply self_case h₄
    · rw [hx25, ht]; ring
    · rw [hy]; simp
  have hD : t + 1 ≠ 0 := by
    intro ht
    exact pow_ne_zero 2 hy (by rw [hySq, ht, mul_zero])
  by_cases hx : x = 0
  · have ht : t = 0 := by simp [t, hx]
    apply flex_case hy
    · simp [hx]
    · simp [hx]
    · rw [hy25, ht, zero_add, one_pow, mul_one]
  by_cases ht : t = 1
  · have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    apply flex_case hy
    · rw [hCube, ht]
      linear_combination (x * A) * h5
    · rw [hx25, ht, one_pow, mul_one]
    · have h12 : (1 + 1 : K) ^ 12 = 1 := by linear_combination 819 * h5
      rw [hy25, ht, h12, mul_one]
  by_cases hV : ordinateFactor t = 0
  · obtain ⟨h₂P, h₂⟩ := double_some hA hy hP
    have hy₂ : (2 * x ^ 6 - A ^ 2) / y ^ 3 = 0 :=
      (normalized_second_coordinates hA hy hD hCube hySq).2.trans (by rw [hV, mul_zero, zero_div])
    have h₄ : (4 : ℕ) • P = 0 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul]
      change 2 • (2 • Affine.Point.some x y hP) = _
      rw [h₂]
      exact (two_nsmul_affine_some_iff two_ne h₂P).mpr hy₂
    obtain ⟨hpow8, hpow12⟩ := fourth_torsion_powers hV
    apply self_case h₄
    · rw [hx25, hpow8, mul_one]
    · rw [hy25, hpow12]; ring
  exact five_some_of_secant hA hA4 hx hy ht hD hV hCube hySq hP

end
end ManuscriptAudit.CubicCharacteristicFiveMultiple

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CubicCharacteristicFiveMultiple.five_some
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
