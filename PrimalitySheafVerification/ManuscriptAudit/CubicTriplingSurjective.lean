import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicTripleAbscissa
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! Multiplication by three is surjective on the actual geometric point group of the centered cubic. -/

namespace ManuscriptAudit.CubicTriplingSurjective

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicTripleAbscissa

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

private theorem centered_negY (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

private theorem centered_addX (x u l : K) : (Curve A).addX x u l = l ^ 2 - x - u := by
  simp [Curve, CubicAffine, shortCubic, Affine.addX]

private theorem centered_addY (x u y l : K) :
    (Curve A).addY x u y l = l * (x - (Curve A).addX x u l) - y := by
  rw [Affine.addY, centered_negY]
  simp only [Affine.negAddY]
  ring

private theorem numerator_factored (A x : K) :
    numerator A x = 64 * (x ^ 3 + A) ^ 3 -
      72 * x ^ 3 * (x ^ 3 + A) * (x ^ 3 + 4 * A) +
      9 * x ^ 3 * (x ^ 3 + 4 * A) ^ 2 := by
  unfold numerator
  ring

set_option maxHeartbeats 500000 in
private theorem triple_some_of_nonzero_ordinate {x y u : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hy : y ≠ 0) (hEq : y ^ 2 = x ^ 3 + A)
    (hD : denominator A x ≠ 0) (hU : numerator A x = u * denominator A x)
    (hP : (Curve A).Nonsingular x y) :
    ∃ v : K, ∃ h : (Curve A).Nonsingular u v,
      (3 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) = Affine.Point.some u v h := by
  let W := Curve A
  let g := x ^ 3 + 4 * A
  have hD' : denominator A x = (3 * x * g) ^ 2 := by
    dsimp only [g, denominator]
    ring
  have hD₀ : 3 * x * g ≠ 0 := by
    intro he
    exact hD (by rw [hD', he, zero_pow (by decide : (2 : ℕ) ≠ 0)])
  have hx₀ : x ≠ 0 := by
    intro h
    exact hD₀ (by rw [h, mul_zero, zero_mul])
  have hg₀ : g ≠ 0 := by
    intro h
    exact hD₀ (by rw [h, mul_zero])
  have h₄ : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero _ h₂
  have hyNeg : y ≠ W.negY x y := by
    change y ≠ (Curve A).negY x y
    rw [centered_negY]
    intro he
    apply mul_ne_zero h₂ hy
    calc
      _ = y + y := two_mul y
      _ = -y + y := congrArg (fun b => b + y) he
      _ = 0 := neg_add_cancel y
  let l := W.slope x x y y
  have hl : l = 3 * x ^ 2 / (2 * y) := by
    change W.slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hyNeg, centered_negY, sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
  let x₂ := W.addX x x l
  let y₂ := W.addY x x y l
  have hX₂ : x₂ = l ^ 2 - x - x := centered_addX x x l
  have hY₂ : y₂ = l * (x - x₂) - y := centered_addY x x y l
  have hdiff : x₂ - x = -(3 * x * g) / (4 * y ^ 2) := by
    rw [hX₂, hl]
    calc
      _ = (9 * x ^ 4 - 12 * x * y ^ 2) / (4 * y ^ 2) := by
        field_simp [h₂, h₄, hy] <;> ring
      _ = _ := by
        apply congrArg (fun a : K => a / (4 * y ^ 2))
        rw [hEq]
        dsimp only [g]
        ring
  have hdiff₀ : x₂ - x ≠ 0 := by
    rw [hdiff]
    exact div_ne_zero (neg_ne_zero.mpr hD₀) (mul_ne_zero h₄ (pow_ne_zero _ hy))
  have hxNe : x ≠ x₂ := (sub_ne_zero.mp hdiff₀).symm
  let m := W.slope x x₂ y y₂
  let s := 8 * y ^ 3 / (3 * x * g)
  have hm : m = s - l := by
    change W.slope x x₂ y y₂ = _
    rw [Affine.slope_of_X_ne hxNe, hY₂]
    calc
      _ = -(2 * y) / (x₂ - x) - l := by
        field_simp [sub_ne_zero.mpr hxNe, hdiff₀] <;> ring
      _ = _ := by
        rw [hdiff]
        dsimp only [s]
        field_simp [h₄, h₃, hy, hx₀, hg₀, hD₀] <;> ring
  have hs₂ : s ^ 2 * denominator A x = 64 * y ^ 6 := by
    rw [hD']
    dsimp only [s]
    field_simp [h₃, hx₀, hg₀, hD₀] <;> ring
  have hls : (2 * l * s) * denominator A x = 72 * x ^ 3 * y ^ 2 * g := by
    rw [hD', hl]
    dsimp only [s]
    field_simp [h₂, h₃, hy, hx₀, hg₀, hD₀] <;> ring
  have hX : W.addX x x₂ m = u := by
    apply mul_right_cancel₀ hD
    calc
      _ = ((s ^ 2 - 2 * l * s) + x) * denominator A x := by
        change ((Curve A).addX x x₂ m) * _ = _
        rw [centered_addX, hX₂, hm]
        ring
      _ = s ^ 2 * denominator A x - (2 * l * s) * denominator A x +
          x * denominator A x := by ring
      _ = 64 * y ^ 6 - 72 * x ^ 3 * y ^ 2 * g + 9 * x ^ 3 * g ^ 2 := by
        rw [hs₂, hls, hD']
        ring
      _ = numerator A x := by
        rw [show y ^ 6 = (y ^ 2) ^ 3 by ring, hEq]
        exact (numerator_factored A x).symm
      _ = _ := hU
  have h₂P : W.Nonsingular x₂ y₂ :=
    Affine.nonsingular_add hP hP (fun h => hyNeg h.2)
  let v := W.addY x x₂ y m
  have h₃P : W.Nonsingular (W.addX x x₂ m) v :=
    Affine.nonsingular_add hP h₂P (fun h => hxNe h.1)
  have hv : W.Nonsingular u v := hX ▸ h₃P
  refine ⟨v, hv, ?_⟩
  rw [show (3 : ℕ) = 1 + 2 by decide, add_nsmul, one_nsmul, two_nsmul,
    Affine.Point.add_of_Y_ne hyNeg]
  change Affine.Point.some x y hP + Affine.Point.some x₂ y₂ h₂P = _
  rw [Affine.Point.add_of_X_ne hxNe, Affine.Point.some.injEq]
  exact ⟨hX, rfl⟩

/-- The native triple of a point with nonvanishing division denominator has the computed abscissa. -/
theorem triple_some {x y u : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (hD : denominator A x ≠ 0) (hU : numerator A x = u * denominator A x)
    (hP : (Curve A).Nonsingular x y) :
    ∃ v : K, ∃ h : (Curve A).Nonsingular u v,
      (3 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) = Affine.Point.some u v h := by
  have hEq := (nonsingular_iff hΔ x y).mp hP
  by_cases hy : y = 0
  · have hf : x ^ 3 + A = 0 := by simpa [hy] using hEq.symm
    have hnum : numerator A x = x * denominator A x := by
      rw [numerator_factored, hf]
      unfold denominator
      ring
    have hxu : x = u := mul_right_cancel₀ hD (hnum.symm.trans hU)
    subst u
    refine ⟨y, hP, ?_⟩
    rw [show (3 : ℕ) = 1 + 2 by decide, add_nsmul, one_nsmul,
      (two_nsmul_affine_some_iff h₂ hP).mpr hy, add_zero]
  · exact triple_some_of_nonzero_ordinate h₂ h₃ hy hEq hD hU hP

variable [IsAlgClosed K]

/-- Geometric tripling is surjective on actual nonsingular affine-model group points. -/
theorem affine_tripling_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Function.Surjective (fun P : (Curve A).Point => (3 : ℕ) • P) := by
  intro Q
  cases Q with
  | zero => exact ⟨0, nsmul_zero _⟩
  | some u v hQ =>
      have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA
      obtain ⟨x, hD, hU⟩ := exists_triple_abscissa h₂ h₃ hA u
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + A) (n := 2) (by decide)
      have hP := (nonsingular_iff hΔ x y).mpr hy
      obtain ⟨w, hw, hTriple⟩ := triple_some h₂ h₃ hΔ hD hU hP
      have hwv : w ^ 2 = v ^ 2 :=
        ((nonsingular_iff hΔ u w).mp hw).trans ((nonsingular_iff hΔ u v).mp hQ).symm
      rcases ordinate_eq_of_two_squares hwv with hplus | hminus
      · refine ⟨Affine.Point.some x y hP, hTriple.trans ?_⟩
        simpa only [Affine.Point.some.injEq, true_and] using hplus
      · have hNeg : (3 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) =
            -(Affine.Point.some u v hQ : (Curve A).Point) := by
          rw [hTriple, Affine.Point.neg_some]
          simpa only [Affine.Point.some.injEq, true_and, centered_negY] using hminus
        refine ⟨-(Affine.Point.some x y hP : (Curve A).Point), ?_⟩
        change (3 : ℕ) • (-(Affine.Point.some x y hP : (Curve A).Point)) = _
        rw [smul_neg, hNeg, neg_neg]

/-- Geometric tripling is surjective on the actual projective cubic. -/
theorem projective_tripling_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Function.Surjective (fun P : (shortCubic (0 : K) A).toProjective.Point => (3 : ℕ) • P) := by
  let e := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) A).toProjective)
  intro Q
  obtain ⟨P, hP⟩ := affine_tripling_surjective h₂ h₃ hA (e Q)
  change (3 : ℕ) • P = e Q at hP
  refine ⟨e.symm P, e.injective ?_⟩
  rw [map_nsmul, e.apply_symm_apply, hP]

end
end ManuscriptAudit.CubicTriplingSurjective

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTriplingSurjective.triple_some,
      ``ManuscriptAudit.CubicTriplingSurjective.affine_tripling_surjective,
      ``ManuscriptAudit.CubicTriplingSurjective.projective_tripling_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
