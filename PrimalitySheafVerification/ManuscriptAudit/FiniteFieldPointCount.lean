import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.Fintype.Option
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPowerSums

/-!
# Finite-field point counts and the Euler criterion

Paper 5, physical PDF pp. 158–162, counts points on the short Weierstrass
equation y² = x³ − p x + A. Below c is the field value of the linear
coefficient parameter p. The formulas count each actual affine solution and,
when the discriminant is nonzero, the actual projective points. Casting into
the finite field reduces these counts modulo its characteristic.
-/

namespace ManuscriptAudit.FiniteFieldPointCount

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The cardinality of the actual square-root fiber, reduced into an odd
finite field, equals the Euler expression at every value of b. -/
theorem squareRootFiber_count_cast (hF : ringChar F ≠ 2) (b : F) :
    ({y : F | y ^ 2 = b}.toFinset.card : F) =
      1 + b ^ ((Fintype.card F - 1) / 2) := by
  have hOdd := FiniteField.odd_card_of_char_ne_two hF
  have hExp : (Fintype.card F - 1) / 2 = Fintype.card F / 2 := by omega
  have hCard : ({y : F | y ^ 2 = b}.toFinset.card : ℤ) = quadraticChar F b + 1 :=
    quadraticChar_card_sqrts hF b
  have hCast : ({y : F | y ^ 2 = b}.toFinset.card : F) = (quadraticChar F b : F) + 1 := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one] using
      congrArg (fun z : ℤ => (z : F)) hCard
  rw [hCast, quadraticChar_eq_pow_of_char_ne_two' hF b, hExp, add_comm]

abbrev QuadraticAffinePoints (f : F → F) :=
  {xy : F × F // xy.2 ^ 2 = f xy.1}

private def affineEquivSigma (f : F → F) :
    QuadraticAffinePoints f ≃ Σ x : F, {y : F // y ^ 2 = f x} where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, xy.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv := by rintro ⟨⟨x, y⟩, h⟩; rfl
  right_inv := by rintro ⟨x, ⟨y, h⟩⟩; rfl

/-- The count of literal affine solutions y²=f(x), reduced into F. -/
theorem affinePoints_count_cast (hF : ringChar F ≠ 2) (f : F → F) :
    (Fintype.card (QuadraticAffinePoints f) : F) =
      ∑ x : F, f x ^ ((Fintype.card F - 1) / 2) := by
  rw [Fintype.card_congr (affineEquivSigma f), Fintype.card_sigma, Nat.cast_sum]
  have hFiber (x : F) : (Fintype.card {y : F // y ^ 2 = f x} : F) =
      1 + f x ^ ((Fintype.card F - 1) / 2) := by
    have hCard : Fintype.card {y : F // y ^ 2 = f x} =
        {y : F | y ^ 2 = f x}.toFinset.card :=
      Fintype.card_of_subtype _ (fun y => by
        simpa only [Set.mem_toFinset, Set.mem_setOf_eq])
    rw [hCard]
    exact squareRootFiber_count_cast hF (f x)
  simp_rw [hFiber]
  rw [Finset.sum_add_distrib]
  have hConst : (∑ _x : F, (1 : F)) = 0 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_one] using
      FiniteField.cast_card_eq_zero F
  rw [hConst, zero_add]

/-- The actual affine point count as an integer, before reduction into the field. -/
theorem affinePoints_count_int (hF : ringChar F ≠ 2) (f : F → F) :
    (Fintype.card (QuadraticAffinePoints f) : ℤ) =
      (Fintype.card F : ℤ) + ∑ x : F, quadraticChar F (f x) := by
  rw [Fintype.card_congr (affineEquivSigma f), Fintype.card_sigma, Nat.cast_sum]
  have hFiber (x : F) : (Fintype.card {y : F // y ^ 2 = f x} : ℤ) =
      quadraticChar F (f x) + 1 := by
    have hCard : Fintype.card {y : F // y ^ 2 = f x} =
        {y : F | y ^ 2 = f x}.toFinset.card :=
      Fintype.card_of_subtype _ (fun y => by
        simpa only [Set.mem_toFinset, Set.mem_setOf_eq])
    rw [hCard]
    exact quadraticChar_card_sqrts hF (f x)
  simp_rw [hFiber]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, add_comm]

/-- The short Weierstrass equation of the printed family over F. -/
def shortCubic (c A : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -c
  a₆ := A

private theorem shortCubic_nonsingular_iff {c A : F}
    (hΔ : (shortCubic c A).Δ ≠ 0) (x y : F) :
    (shortCubic c A).toProjective.toAffine.Nonsingular x y ↔
      y ^ 2 = x ^ 3 - c * x + A := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ,
    WeierstrassCurve.Affine.equation_iff]
  simp [shortCubic, sub_eq_add_neg, neg_mul]

private def shortCubicProjectiveEquiv {c A : F} (hΔ : (shortCubic c A).Δ ≠ 0) :
    (shortCubic c A).toProjective.Point ≃
      Option (QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A)) := by
  classical
  let W := (shortCubic c A).toProjective
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} ≃
      QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A) :=
    { toFun := fun xy => ⟨xy.1, (shortCubic_nonsingular_iff hΔ _ _).1 xy.2⟩
      invFun := fun xy => ⟨xy.1, (shortCubic_nonsingular_iff hΔ _ _).2 xy.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans e₃.optionCongr)

/-- The count of actual projective points, reduced into the finite field. -/
theorem shortCubic_projective_count_cast (hF : ringChar F ≠ 2) {c A : F}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    (Nat.card (shortCubic c A).toProjective.Point : F) =
      1 + ∑ x : F, (x ^ 3 - c * x + A) ^ ((Fintype.card F - 1) / 2) := by
  have hCard : Nat.card (shortCubic c A).toProjective.Point =
      Fintype.card (QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A)) + 1 := by
    calc
      _ = Nat.card (Option (QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A))) :=
        Nat.card_congr (shortCubicProjectiveEquiv hΔ)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_option]
  rw [hCard, Nat.cast_add, Nat.cast_one, affinePoints_count_cast hF]
  exact add_comm _ _

/-- The exact projective count with the quadratic character over the integers. -/
theorem shortCubic_projective_count_int (hF : ringChar F ≠ 2) {c A : F}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    (Nat.card (shortCubic c A).toProjective.Point : ℤ) =
      (Fintype.card F : ℤ) + 1 + ∑ x : F, quadraticChar F (x ^ 3 - c * x + A) := by
  classical
  have hCard : Nat.card (shortCubic c A).toProjective.Point =
      Fintype.card (QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A)) + 1 := by
    calc
      _ = Nat.card (Option (QuadraticAffinePoints (fun x : F => x ^ 3 - c * x + A))) :=
        Nat.card_congr (shortCubicProjectiveEquiv hΔ)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_option]
  rw [hCard, Nat.cast_add, Nat.cast_one, affinePoints_count_int hF]
  ac_rfl

/-- The projective point count of the reduced cubic is one minus
the indicated polynomial coefficient after reduction to the field. -/
theorem shortCubic_zero_count_cast_eq_one_sub_coeff (hF : ringChar F ≠ 2)
    (hq : 1 < Fintype.card F) {A : F} (hΔ : (shortCubic (0 : F) A).Δ ≠ 0) :
    (Nat.card (shortCubic (0 : F) A).toProjective.Point : F) =
      1 - (((Polynomial.X : Polynomial F) ^ 3 + Polynomial.C A) ^
        ((Fintype.card F - 1) / 2)).coeff (Fintype.card F - 1) := by
  let n := (Fintype.card F - 1) / 2
  let f := ((Polynomial.X : Polynomial F) ^ 3 + Polynomial.C A) ^ n
  have hbase : ((Polynomial.X : Polynomial F) ^ 3 + Polynomial.C A).natDegree ≤ 3 :=
    (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hf : f.natDegree < (Fintype.card F - 1) * 2 := by
    calc
      _ = n * ((Polynomial.X : Polynomial F) ^ 3 + Polynomial.C A).natDegree :=
        Polynomial.natDegree_pow _ _
      _ ≤ n * 3 := Nat.mul_le_mul_left _ hbase
      _ < (Fintype.card F - 1) * 2 := by dsimp [n]; omega
  have he (t : F) : f.eval t = (t ^ 3 + A) ^ n := by simp [f]
  rw [shortCubic_projective_count_cast hF hΔ]
  simp only [zero_mul, sub_zero]
  change (1 : F) + (∑ t : F, (t ^ 3 + A) ^ n) = 1 - f.coeff (Fintype.card F - 1)
  simp_rw [← he]
  rw [_root_.ManuscriptAudit.FiniteFieldPowerSums.finite_field_sum_eval_eq_neg_coeff F hq f hf,
    sub_eq_add_neg]

end

end ManuscriptAudit.FiniteFieldPointCount

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.FiniteFieldPointCount.squareRootFiber_count_cast,
    ``ManuscriptAudit.FiniteFieldPointCount.affinePoints_count_cast,
    ``ManuscriptAudit.FiniteFieldPointCount.affinePoints_count_int,
    ``ManuscriptAudit.FiniteFieldPointCount.shortCubic_projective_count_cast,
    ``ManuscriptAudit.FiniteFieldPointCount.shortCubic_projective_count_int,
    ``ManuscriptAudit.FiniteFieldPointCount.shortCubic_zero_count_cast_eq_one_sub_coeff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
