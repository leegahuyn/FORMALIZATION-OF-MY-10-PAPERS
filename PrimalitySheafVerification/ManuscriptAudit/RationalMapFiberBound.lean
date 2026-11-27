import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAbscissaPair
import PrimalitySheafVerification.ManuscriptAudit.RationalSubstitutionDegree

/-! Specializing a literal rational abscissa puts each input into a bounded-degree root set. -/

namespace ManuscriptAudit.RationalMapFiberBound

open Polynomial CubicGenericFunctionField CubicGenericAbscissaPair RationalSubstitutionDegree

noncomputable section

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The equation for a finite abscissa fiber of a normalized rational function. -/
def fiberPolynomial (f : RatFunc K) (t : M) : M[X] :=
  f.num.map (algebraMap K M) - C t * f.denom.map (algebraMap K M)

theorem natDegree_fiberPolynomial_le (f : RatFunc K) (t : M) :
    (fiberPolynomial f t).natDegree ≤ rationalDegree f := by
  unfold fiberPolynomial rationalDegree
  have hN : (f.num.map (algebraMap K M)).natDegree = f.num.natDegree :=
    natDegree_map_eq_of_injective (algebraMap K M).injective f.num
  have hD : (f.denom.map (algebraMap K M)).natDegree = f.denom.natDegree :=
    natDegree_map_eq_of_injective (algebraMap K M).injective f.denom
  have hMul : (C t * f.denom.map (algebraMap K M)).natDegree ≤ f.denom.natDegree := by
    calc
      _ ≤ (C t).natDegree + (f.denom.map (algebraMap K M)).natDegree := natDegree_mul_le
      _ = _ := by rw [natDegree_C, zero_add, hD]
  exact (natDegree_sub_le _ _).trans (max_le_max hN.le hMul)

/-- A transcendental target cannot make the fiber equation identically zero. -/
theorem fiberPolynomial_ne_zero (f : RatFunc K) (t : M) (ht : Transcendental K t) :
    fiberPolynomial f t ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  let n := f.denom.natDegree
  have hn : f.denom.coeff n = 1 := RatFunc.monic_denom f
  have hcoeff := congrArg (fun p : M[X] => p.coeff n) he
  simp only [coeff_map, coeff_C_mul, hn, map_one, mul_one] at hcoeff
  exact ht (hcoeff ▸ isAlgebraic_algebraMap (A := M) (f.num.coeff n))

private theorem polynomialValue (A : K) (g : Model A →ₐ[K] M) (p : K[X]) :
    g (coeffMap A p) = (p.map (algebraMap K M)).eval (g (genericX A)) := by
  let φ : K[X] →ₐ[K] M :=
    (g.comp (IsScalarTower.toAlgHom K (RatFunc K) (Model A))).comp
      (IsScalarTower.toAlgHom K K[X] (RatFunc K))
  have hX : φ X = g (genericX A) := by
    change g (algebraMap (RatFunc K) (Model A) (algebraMap K[X] (RatFunc K) X)) = _
    rw [RatFunc.algebraMap_X, genericX]
  change φ p = _
  rw [Polynomial.eval_unique φ, hX, eval_map]

/-- Evaluation of any actual generic rational coordinate gives a root of the fiber polynomial. -/
theorem isRoot_of_specialization (A : K) (g : Model A →ₐ[K] M) (f : RatFunc K) :
    (fiberPolynomial f (g (algebraMap (RatFunc K) (Model A) f))).IsRoot
      (g (genericX A)) := by
  let e := algebraMap K[X] (RatFunc K)
  have hD : e f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have he : e f.num = f * e f.denom := (div_eq_iff hD).mp (RatFunc.num_div_denom f)
  have h := congrArg (fun x : RatFunc K => g (algebraMap (RatFunc K) (Model A) x)) he
  simp only [map_mul] at h
  change g (coeffMap A f.num) = g (algebraMap (RatFunc K) (Model A) f) *
    g (coeffMap A f.denom) at h
  rw [polynomialValue, polynomialValue] at h
  change (fiberPolynomial f (g (algebraMap (RatFunc K) (Model A) f))).eval
    (g (genericX A)) = 0
  simp only [fiberPolynomial, eval_sub, eval_mul, eval_C]
  exact sub_eq_zero.mpr h

end

end ManuscriptAudit.RationalMapFiberBound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RationalMapFiberBound.natDegree_fiberPolynomial_le,
      ``ManuscriptAudit.RationalMapFiberBound.fiberPolynomial_ne_zero,
      ``ManuscriptAudit.RationalMapFiberBound.isRoot_of_specialization] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
