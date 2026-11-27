import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerSecant

/-! Exact homogeneous addition-and-subtraction formulas on the actual centered cubic point group. -/

namespace ManuscriptAudit.CubicKummerPoints

open WeierstrassCurve CubicKummerQuadratic CubicKummerSecant CubicThreeTorsionOrdinate
open FiniteFieldPointCount CubicTwoTorsion

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

private theorem negY_formula (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

private theorem sym2x_diagonal (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (x y : K) (hP : (Curve A).Nonsingular x y) :
    let P : (Curve A).Point := .some x y hP
    ∃ c : K, c ≠ 0 ∧ forms A (P.sym2x P) = fun i => c * ((P + P).sym2x (P - P) i) := by
  let P : (Curve A).Point := .some x y hP
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA
  have hyq := (nonsingular_iff hΔ x y).mp hP
  change ∃ c : K, c ≠ 0 ∧ forms A (P.sym2x P) = fun i => c * ((P + P).sym2x (P - P) i)
  rw [sub_self]
  by_cases hy : y = 0
  · have hpp : P + P = 0 := Affine.Point.add_of_Y_eq rfl (by rw [negY_formula, hy, neg_zero])
    rw [hpp, Affine.Point.sym2x_zero_zero]
    have hB : x ^ 3 + A = 0 := by simpa [hy] using hyq.symm
    have hx : x ≠ 0 := by
      intro he
      exact hA (by simpa [he] using hB)
    have hVal : x ^ 4 - 8 * A * x = (3 : K) ^ 2 * x ^ 4 := by
      have hB' : A = -(x ^ 3) := eq_neg_of_add_eq_zero_right hB
      rw [hB']
      ring
    refine ⟨x ^ 4 - 8 * A * x, by
      rw [hVal]
      exact mul_ne_zero (pow_ne_zero _ h₃) (pow_ne_zero _ hx), ?_⟩
    change forms A ((Affine.Point.some x y hP).sym2x _) = _
    rw [Affine.Point.sym2x_some_some]
    ext i
    fin_cases i <;> simp [forms] <;> ring_nf at hB ⊢ <;> linear_combination hB
  · have hY : y ≠ (Curve A).negY x y := by
      rw [negY_formula]
      intro h
      have hz : (2 : K) * y = 0 := by linear_combination h
      exact (mul_ne_zero h₂ hy) hz
    have hScale : (4 : K) * y ^ 2 ≠ 0 := by
      have h4 : (4 : K) = 2 ^ 2 := by ring
      rw [h4]
      exact mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ hy)
    refine ⟨4 * y ^ 2, hScale, ?_⟩
    change forms A ((Affine.Point.some x y hP).sym2x (.some x y hP)) =
      fun i => (4 * y ^ 2) * (((Affine.Point.some x y hP) + (.some x y hP)).sym2x 0 i)
    rw [Affine.Point.add_of_Y_ne hY, Affine.Point.sym2x_some_zero, Affine.Point.sym2x_some_some,
      Affine.slope_of_Y_ne rfl hY, negY_formula]
    have hDen : y - -y ≠ 0 := sub_ne_zero.mpr (by simpa [negY_formula] using hY)
    ext i
    fin_cases i
    · simp [forms, Curve, CubicAffine, shortCubic, Affine.addX]
      field_simp [hDen]
      linear_combination 32 * x * y ^ 2 * hyq
    · simp [forms]
      linear_combination -4 * hyq
    · simp [forms]
      ring

/-- The basepoint-free forms yield exactly the unordered pair of actual sum/difference abscissas. -/
theorem sym2x_add_sub (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (P Q : (Curve A).Point) :
    ∃ c : K, c ≠ 0 ∧ forms A (P.sym2x Q) = fun i => c * ((P + Q).sym2x (P - Q) i) := by
  cases P with
  | zero =>
    cases Q with
    | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      change forms A ((0 : (Curve A).Point).sym2x 0) = fun i =>
        1 * (((0 : (Curve A).Point) + 0).sym2x (0 - 0) i)
      simp only [zero_add, sub_self, one_mul, Affine.Point.sym2x_zero_zero]
      ext i
      fin_cases i <;> simp [forms]
    | some z w hQ =>
      refine ⟨1, one_ne_zero, ?_⟩
      let Q : (Curve A).Point := .some z w hQ
      change forms A ((0 : (Curve A).Point).sym2x Q) = fun i =>
        1 * ((0 + Q).sym2x (0 - Q) i)
      simp only [zero_add, zero_sub, one_mul, Affine.Point.sym2x_neg_right]
      change forms A ((0 : (Curve A).Point).sym2x (.some z w hQ)) =
        fun i => ((Affine.Point.some z w hQ).sym2x (.some z w hQ)) i
      rw [Affine.Point.sym2x_zero_some, Affine.Point.sym2x_some_some]
      ext i
      fin_cases i <;> simp [forms] <;> ring
  | some x y hP =>
    cases Q with
    | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      let P : (Curve A).Point := .some x y hP
      change forms A (P.sym2x 0) = fun i => 1 * ((P + 0).sym2x (P - 0) i)
      simp only [add_zero, sub_zero, one_mul]
      change forms A ((Affine.Point.some x y hP).sym2x 0) =
        fun i => ((Affine.Point.some x y hP).sym2x (.some x y hP)) i
      rw [Affine.Point.sym2x_some_zero, Affine.Point.sym2x_some_some]
      ext i
      fin_cases i <;> simp [forms] <;> ring
    | some z w hQ =>
      have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA
      have hy := (nonsingular_iff hΔ x y).mp hP
      have hw := (nonsingular_iff hΔ z w).mp hQ
      by_cases hxz : x = z
      · subst z
        rcases ordinate_eq_of_two_squares (hw.trans hy.symm) with he | he
        · subst w
          exact sym2x_diagonal h₂ h₃ hA x y hP
        · let P : (Curve A).Point := .some x y hP
          have hQ' : (Affine.Point.some x w hQ : (Curve A).Point) = -P := by
            rw [show -P = -(.some x y hP : (Curve A).Point) by rfl, Affine.Point.neg_some,
              Affine.Point.some.injEq, negY_formula]
            exact ⟨rfl, he⟩
          rw [hQ']
          obtain ⟨c, hc, hs⟩ := sym2x_diagonal h₂ h₃ hA x y hP
          refine ⟨c, hc, ?_⟩
          change forms A (P.sym2x (-P)) = fun i => c * ((P + -P).sym2x (P - -P) i)
          rw [Affine.Point.sym2x_neg_right, ← sub_eq_add_neg, sub_neg_eq_add,
            Affine.Point.sym2x_comm (P - P) (P + P)]
          exact hs
      · let hQ' : (Curve A).Nonsingular z (-w) :=
          (nonsingular_iff hΔ z (-w)).mpr (by simpa using hw)
        have hNeg : -(Affine.Point.some z w hQ : (Curve A).Point) = .some z (-w) hQ' := by
          rw [Affine.Point.neg_some, Affine.Point.some.injEq, negY_formula]
          exact ⟨rfl, rfl⟩
        refine ⟨(x - z) ^ 2, pow_ne_zero _ (sub_ne_zero.mpr hxz), ?_⟩
        rw [sub_eq_add_neg, hNeg, Affine.Point.add_of_X_ne (h₁ := hP) (h₂ := hQ) hxz,
          Affine.Point.add_of_X_ne (h₁ := hP) (h₂ := hQ') hxz]
        simp only [Affine.Point.sym2x_some_some, Affine.slope_of_X_ne hxz]
        simpa [Curve, CubicAffine, shortCubic, Affine.addX, sub_neg_eq_add] using secant_forms hxz hy hw

end ManuscriptAudit.CubicKummerPoints

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicKummerPoints.sym2x_add_sub
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
