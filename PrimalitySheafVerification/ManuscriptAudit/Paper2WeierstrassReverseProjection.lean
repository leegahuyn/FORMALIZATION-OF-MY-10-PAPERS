import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassEtaleProjection

/-! The second affine projection uses the genuine coordinate algebra with the variables exchanged. -/

namespace ManuscriptAudit.Paper2WeierstrassReverseProjection

open Algebra WeierstrassCurve Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The original Weierstrass relation, with the variables exchanged and leading sign normalized. -/
def polynomialInX (W : WeierstrassCurve R) : (Polynomial R)[X] :=
  (⟨1, C W.a₂, C W.a₄ - C W.a₁ * X, C W.a₆ - X ^ 2 - C W.a₃ * X⟩ :
    Cubic (Polynomial R)).toPoly

theorem polynomialInX_monic (W : WeierstrassCurve R) :
    (polynomialInX W).Monic :=
  Cubic.monic_of_a_eq_one'

/-- Exchanging the variables carries the literal defining ideal onto the reversed one. -/
theorem swap_polynomial (W : WeierstrassCurve R) :
    Bivariate.swap W.toAffine.polynomial = -polynomialInX W := by
  unfold Affine.polynomial polynomialInX Cubic.toPoly
  simp only [map_add, map_sub, map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_Y,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Cubic.a, Cubic.b, Cubic.c, Cubic.d, C_one, one_mul, C_sub]
  ring

/-- The actual original affine ring and the exchanged presentation describe the same curve. -/
def swapPresentation (W : WeierstrassCurve R) :
    W.toAffine.CoordinateRing ≃ₐ[R] AdjoinRoot (polynomialInX W) := by
  apply Ideal.quotientEquivAlg _ _ (Bivariate.swap (R := R))
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {polynomialInX W} = Ideal.span {Bivariate.swap W.toAffine.polynomial}
  rw [swap_polynomial, Ideal.span_singleton_neg]

theorem swapPresentation_y (W : WeierstrassCurve R) :
    swapPresentation W (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.of (polynomialInX W) X := by
  change AdjoinRoot.mk (polynomialInX W) (Bivariate.swap (R := R) X) =
    AdjoinRoot.mk (polynomialInX W) (C X)
  rw [Bivariate.swap_Y]

theorem swapPresentation_x (W : WeierstrassCurve R) :
    swapPresentation W (AdjoinRoot.of W.toAffine.polynomial X) =
      AdjoinRoot.root (polynomialInX W) := by
  change AdjoinRoot.mk (polynomialInX W) (Bivariate.swap (R := R) (C X)) =
    AdjoinRoot.mk (polynomialInX W) X
  rw [Bivariate.swap_X]

theorem derivative_eval (W : WeierstrassCurve R) (x y : R) :
    (polynomialInX W).derivative.evalEval y x = -W.toAffine.polynomialX.evalEval x y := by
  rw [Affine.evalEval_polynomialX]
  simp only [polynomialInX, Cubic.toPoly, Cubic.a, Cubic.b, Cubic.c, Cubic.d, C_one, one_mul,
    derivative_add, derivative_C, derivative_C_mul, derivative_X_pow, derivative_X, mul_one,
    add_zero, evalEval_add, evalEval_mul, evalEval_pow, evalEval_X, evalEval_C, eval_add,
    eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_natCast]
  norm_num <;> ring

private def standardPair (W : WeierstrassCurve R) : StandardEtalePair (Polynomial R) where
  f := polynomialInX W
  monic_f := polynomialInX_monic W
  g := (polynomialInX W).derivative
  cond := ⟨1, 0, 1, by simp⟩

abbrev ReverseProjectionChart (W : WeierstrassCurve R) :=
  Localization.Away (AdjoinRoot.mk (polynomialInX W) (polynomialInX W).derivative)

theorem projection_etale (W : WeierstrassCurve R) :
    Algebra.Etale (Polynomial R) (ReverseProjectionChart W) :=
  Algebra.Etale.of_equiv (standardPair W).equivAwayAdjoinRoot

theorem projection_square_zero_unique (W : WeierstrassCurve R)
    (B : Type*) [CommRing B] [Algebra (Polynomial R) B]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ (Polynomial R) I).comp :
      (ReverseProjectionChart W →ₐ[Polynomial R] B) → ReverseProjectionChart W →ₐ[Polynomial R] B ⧸ I) := by
  letI := projection_etale W
  exact Algebra.FormallyEtale.comp_bijective (Polynomial R) (ReverseProjectionChart W) I hI

end
end ManuscriptAudit.Paper2WeierstrassReverseProjection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.swap_polynomial,
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.swapPresentation_y,
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.swapPresentation_x,
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.derivative_eval,
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.projection_etale,
      ``ManuscriptAudit.Paper2WeierstrassReverseProjection.projection_square_zero_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
