import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Clearing denominators in homogeneous polynomial equations over K(t)

A single nonzero common denominator clears all coefficients and leaves
the homogeneous degree unchanged. A nonzero solution over the polynomial
ring then gives a nonzero rational solution of the original equation.
-/

namespace ManuscriptAudit.RatFuncHomogeneousDenominator

open MvPolynomial
open scoped nonZeroDivisors BigOperators

noncomputable section

variable (K : Type*) [Field K]

/-- Clear a finite family of rational coefficients with one denominator,
without changing the monomial degrees. -/
theorem clearDenominator {ι : Type*} {d : ℕ} (P : MvPolynomial ι (RatFunc K))
    (hP : P.IsHomogeneous d) :
    ∃ q : Polynomial K, q ≠ 0 ∧ ∃ Q : MvPolynomial ι (Polynomial K), Q.IsHomogeneous d ∧
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) Q =
        MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) q) * P := by
  classical
  let a := algebraMap (Polynomial K) (RatFunc K)
  let M := (Polynomial K)⁰
  let s := P.support
  let c := fun i => P.coeff i
  let q := IsLocalization.commonDenom M s c
  let b := fun i : s => IsLocalization.integerMultiple M s c i
  let Q : MvPolynomial ι (Polynomial K) := ∑ i ∈ s.attach, monomial i.val (b i)
  refine ⟨q.val, mem_nonZeroDivisors_iff_ne_zero.mp q.property, Q, ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro i _
    apply isHomogeneous_monomial
    exact ((hP.degree_eq_sum_deg_support i.property).trans
      (Finsupp.degree_apply i.val).symm).symm
  · have hz (i : s) : a (b i) = a q.val * c i.val := by
      rw [← Algebra.smul_def]
      exact IsLocalization.map_integerMultiple M s c i
    change MvPolynomial.map a (∑ i ∈ s.attach, monomial i.val (b i)) = C (a q.val) * P
    calc
      _ = ∑ i ∈ s.attach, monomial i.val (a q.val * c i.val) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_monomial, hz]
      _ = C (a q.val) * ∑ i ∈ s.attach, monomial i.val (c i.val) := by
        rw [Finset.mul_sum]
        simp only [C_mul_monomial]
      _ = C (a q.val) * P := by
        rw [Finset.sum_attach]
        exact congrArg (fun p => C (a q.val) * p) (support_sum_monomial_coeff P)

/-- A polynomial-vector solution of the cleared equation solves the original
one after embedding the polynomial ring in the rational function field. -/
theorem evaluateCleared {ι : Type*} {P : MvPolynomial ι (RatFunc K)}
    {Q : MvPolynomial ι (Polynomial K)} {q : Polynomial K}
    (hq : q ≠ 0) (h : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) Q =
      C (algebraMap (Polynomial K) (RatFunc K) q) * P)
    {x : ι → Polynomial K} (hx : x ≠ 0) (hxQ : aeval x Q = 0) :
    ∃ y : ι → RatFunc K, y ≠ 0 ∧ aeval y P = 0 := by
  let a := algebraMap (Polynomial K) (RatFunc K)
  let y := fun i => a (x i)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx
    funext i
    apply RatFunc.algebraMap_injective K
    simpa only [map_zero] using congrFun hy i
  · have he : a (aeval x Q) = aeval y (MvPolynomial.map a Q) := by
      simpa only [aeval_eq_eval, RingHom.comp_id, eval₂_eq_eval_map] using
        (map_eval₂Hom (RingHom.id (Polynomial K)) x a Q)
    rw [hxQ, map_zero, h, map_mul, aeval_C] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by
      simpa using RatFunc.algebraMap_ne_zero hq)

end

end ManuscriptAudit.RatFuncHomogeneousDenominator

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncHomogeneousDenominator.clearDenominator,
      ``ManuscriptAudit.RatFuncHomogeneousDenominator.evaluateCleared] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
