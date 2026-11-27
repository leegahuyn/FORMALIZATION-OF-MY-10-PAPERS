import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralChartTransition

/-! Evaluating either literal plane chart is equivalent to giving the two
coordinates satisfying its displayed equation. The statement is over
arbitrary coefficient rings, so it also covers valuation rings. -/

namespace ManuscriptAudit.NodalChartPoints

open Polynomial NodalIntegralChartTransition

noncomputable section

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (c : R →+* S)

private theorem z_vanish (x y : S) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (zEquation R).eval₂ (Polynomial.eval₂RingHom c x) y = 0 := by
  unfold zEquation
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change y ^ 2 - ((X : Polynomial R) ^ 2 * (X + 1)).eval₂ c x = 0
  simp only [eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_one, sub_eq_zero]
  exact h

private theorem y_vanish (x z : S) (h : z = x ^ 2 * (x + z)) :
    (yEquation R).eval₂ (Polynomial.eval₂RingHom c x) z = 0 := by
  unfold yEquation
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_X, eval₂_C]
  change z - ((X : Polynomial R) ^ 2).eval₂ c x * ((X : Polynomial R).eval₂ c x + z) = 0
  simp only [eval₂_pow, eval₂_X, sub_eq_zero]
  exact h

/-- Evaluation of the actual plane chart Z=1 at two coordinates. -/
def zEval (x y : S) (h : y ^ 2 = x ^ 2 * (x + 1)) : zChart R →+* S :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom c x) y (z_vanish c x y h)

/-- Evaluation of the actual plane chart Y=1 at two coordinates. -/
def yEval (x z : S) (h : z = x ^ 2 * (x + z)) : yChart R →+* S :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom c x) z (y_vanish c x z h)

@[simp] theorem zEval_x (x y : S) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    zEval c x y h (xZ R) = x :=
  (AdjoinRoot.lift_of (z_vanish c x y h)).trans (Polynomial.eval₂_X _ _)

@[simp] theorem zEval_y (x y : S) (h : y ^ 2 = x ^ 2 * (x + 1)) :
    zEval c x y h (yZ R) = y :=
  AdjoinRoot.lift_root (z_vanish c x y h)

@[simp] theorem yEval_x (x z : S) (h : z = x ^ 2 * (x + z)) :
    yEval c x z h (xY R) = x :=
  (AdjoinRoot.lift_of (y_vanish c x z h)).trans (Polynomial.eval₂_X _ _)

@[simp] theorem yEval_z (x z : S) (h : z = x ^ 2 * (x + z)) :
    yEval c x z h (zY R) = z :=
  AdjoinRoot.lift_root (y_vanish c x z h)

@[simp] theorem zEval_coeff (x y : S) (h : y ^ 2 = x ^ 2 * (x + 1)) (a : R) :
    zEval c x y h (algebraMap R (zChart R) a) = c a :=
  (AdjoinRoot.lift_of (z_vanish c x y h)).trans (Polynomial.eval₂_C _ _)

@[simp] theorem yEval_coeff (x z : S) (h : z = x ^ 2 * (x + z)) (a : R) :
    yEval c x z h (algebraMap R (yChart R) a) = c a :=
  (AdjoinRoot.lift_of (y_vanish c x z h)).trans (Polynomial.eval₂_C _ _)

/-- A homomorphism on the presented plane algebra is uniquely determined
by the images of the coefficient ring and both coordinate functions. -/
theorem planeHom_ext {p : Polynomial (Polynomial R)}
    {f g : AdjoinRoot p →+* S}
    (hC : ∀ a : R, f (algebraMap R (AdjoinRoot p) a) = g (algebraMap R (AdjoinRoot p) a))
    (hX : f (AdjoinRoot.of p X) = g (AdjoinRoot.of p X))
    (hY : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  refine AdjoinRoot.ringHom_ext ?_ hY
  apply RingHom.ext
  intro a
  induction a using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (hC a) (congrArg (· ^ n) hX)

end
end ManuscriptAudit.NodalChartPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartPoints.zEval_x,
      ``ManuscriptAudit.NodalChartPoints.zEval_y,
      ``ManuscriptAudit.NodalChartPoints.yEval_x,
      ``ManuscriptAudit.NodalChartPoints.yEval_z,
      ``ManuscriptAudit.NodalChartPoints.zEval_coeff,
      ``ManuscriptAudit.NodalChartPoints.yEval_coeff,
      ``ManuscriptAudit.NodalChartPoints.planeHom_ext] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
