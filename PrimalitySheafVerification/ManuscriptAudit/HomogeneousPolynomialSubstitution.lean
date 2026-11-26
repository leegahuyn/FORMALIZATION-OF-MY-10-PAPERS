import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial degree bounds for the substitution in Tsen's theorem

If the coefficients of a homogeneous polynomial over `K[t]` have
degree at most `L`, substituting polynomials of degree at most `N`
gives a polynomial of degree at most `L + d * N`, where `d` is the
homogeneous degree. The same bound holds after mapping coefficients
into an auxiliary commutative semiring.
-/

namespace ManuscriptAudit.HomogeneousPolynomialSubstitution

open scoped BigOperators

private theorem natDegree_sum_le {ι R : Type*} [Semiring R] (s : Finset ι)
    (f : ι → Polynomial R) (m : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ m) :
    (∑ i ∈ s, f i).natDegree ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact Polynomial.natDegree_add_le_of_degree_le
      (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem natDegree_prod_le {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → Polynomial R) (m : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ m i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact Polynomial.natDegree_mul_le_of_le
      (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Substitute bounded-degree polynomials into a homogeneous multivariate polynomial. -/
theorem natDegree_eval₂_le {ι K R : Type*} [CommSemiring K] [CommSemiring R]
    (P : MvPolynomial ι (Polynomial K)) {d L N : ℕ}
    (hP : P.IsHomogeneous d) (hL : ∀ i ∈ P.support, (P.coeff i).natDegree ≤ L)
    (φ : K →+* R) (x : ι → Polynomial R) (hN : ∀ i, (x i).natDegree ≤ N) :
    (P.eval₂ (Polynomial.mapRingHom φ) x).natDegree ≤ L + d * N := by
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le
  intro m hm
  apply Polynomial.natDegree_mul_le_of_le
  · change ((P.coeff m).map φ).natDegree ≤ L
    exact Polynomial.natDegree_map_le.trans (hL m hm)
  · have hProduct := natDegree_prod_le m.support (fun i => x i ^ m i)
      (fun i => m i * N) (fun i _ => Polynomial.natDegree_pow_le_of_le (m i) (hN i))
    rw [← Finset.sum_mul, ← hP.degree_eq_sum_deg_support hm] at hProduct
    exact hProduct

end ManuscriptAudit.HomogeneousPolynomialSubstitution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.HomogeneousPolynomialSubstitution.natDegree_eval₂_le
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
