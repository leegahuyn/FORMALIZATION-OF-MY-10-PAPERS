import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicDoubleAbscissa
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! The native doubling homomorphism is surjective over the algebraic closure of a good centered cubic. -/

namespace ManuscriptAudit.CubicDoublingSurjective

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionCard
open CubicThreeTorsionOrdinate CubicDoubleAbscissa

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

private theorem negY_formula (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

private theorem double_abscissa_coordinates {u x y : K}
    (h₂ : (2 : K) ≠ 0) (hy : y ≠ 0) (hyq : y ^ 2 = x ^ 3 + A)
    (hquart : x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) = 0)
    (hP : (Curve A).Nonsingular x y) :
    ∃ v : K, ∃ hv : (Curve A).Nonsingular u v,
      (2 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) = Affine.Point.some u v hv := by
  let W := Curve A
  have hden₀ : (2 : K) * y ≠ 0 := mul_ne_zero h₂ hy
  have hyNeg : y ≠ W.negY x y := by
    change y ≠ (Curve A).negY x y
    rw [negY_formula]
    intro he
    apply hden₀
    calc
      _ = y + y := two_mul y
      _ = (-y) + y := congrArg (fun a => a + y) he
      _ = 0 := neg_add_cancel y
  let ell := W.slope x x y y
  have hslope : ell = (3 * x ^ 2) / (2 * y) := by
    change W.slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hyNeg, negY_formula, sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
  have hmul : ell * ((2 : K) * y) = 3 * x ^ 2 := by
    rw [hslope, div_mul_cancel₀ _ hden₀]
  have hden : ((2 : K) * y) ^ 2 = 4 * (x ^ 3 + A) := by
    calc
      _ = 4 * y ^ 2 := by ring
      _ = _ := by rw [hyq]
  have hX : W.addX x x ell = ell ^ 2 - x - x := by
    simp [W, Curve, CubicAffine, shortCubic, Affine.addX]
  have hprod : (W.addX x x ell - u) * ((2 : K) * y) ^ 2 = 0 := by
    calc
      _ = (ell * ((2 : K) * y)) ^ 2 - (x + x + u) * ((2 : K) * y) ^ 2 := by rw [hX]; ring
      _ = x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) := by rw [hmul, hden]; ring
      _ = 0 := hquart
  have hu : W.addX x x ell = u :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero _ hden₀))
  let v := W.addY x x y ell
  have hh : W.Nonsingular (W.addX x x ell) v :=
    Affine.nonsingular_add hP hP (fun h => hyNeg h.2)
  have hv : W.Nonsingular u v := hu ▸ hh
  refine ⟨v, hv, ?_⟩
  rw [two_nsmul, Affine.Point.add_of_Y_ne hyNeg]
  rw [Affine.Point.some.injEq]
  change W.addX x x ell = u ∧ v = v
  exact ⟨hu, rfl⟩

variable [IsAlgClosed K]

/-- Every actual affine point has a preimage under the native doubling operation. -/
theorem affine_doubling_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) : Function.Surjective (fun P : (Curve A).Point => (2 : ℕ) • P) := by
  intro Q
  cases Q with
  | zero => exact ⟨0, nsmul_zero _⟩
  | some u v hQ =>
    have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ hA
    obtain ⟨x, hx, hquart⟩ := exists_double_abscissa h₃ hA u
    obtain ⟨y, hyq⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + A) (n := 2) (by decide)
    have hy : y ≠ 0 := by
      intro he
      exact hx (by simpa [he] using hyq.symm)
    have hP := (nonsingular_iff hΔ x y).mpr hyq
    let P : (Curve A).Point := .some x y hP
    obtain ⟨w, hw, hDouble⟩ := double_abscissa_coordinates h₂ hy hyq hquart hP
    have hwv : w ^ 2 = v ^ 2 :=
      ((nonsingular_iff hΔ u w).mp hw).trans ((nonsingular_iff hΔ u v).mp hQ).symm
    rcases ordinate_eq_of_two_squares hwv with hplus | hminus
    · refine ⟨P, hDouble.trans ?_⟩
      simpa only [Affine.Point.some.injEq, true_and] using hplus
    · have hNeg : (2 : ℕ) • P = -(Affine.Point.some u v hQ : (Curve A).Point) := by
        rw [hDouble, Affine.Point.neg_some]
        simpa only [Affine.Point.some.injEq, true_and, negY_formula] using hminus
      exact ⟨-P, by rw [smul_neg, hNeg, neg_neg]⟩

/-- Every actual projective point has a preimage under doubling. -/
theorem projective_doubling_surjective (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) : Function.Surjective
      (fun P : (shortCubic (0 : K) A).toProjective.Point => (2 : ℕ) • P) := by
  let e := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) A).toProjective)
  intro Q
  obtain ⟨P, hP⟩ := affine_doubling_surjective h₂ h₃ hA (e Q)
  change (2 : ℕ) • P = e Q at hP
  refine ⟨e.symm P, e.injective ?_⟩
  rw [map_nsmul, e.apply_symm_apply, hP]

end
end ManuscriptAudit.CubicDoublingSurjective

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicDoublingSurjective.affine_doubling_surjective,
      ``ManuscriptAudit.CubicDoublingSurjective.projective_doubling_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
