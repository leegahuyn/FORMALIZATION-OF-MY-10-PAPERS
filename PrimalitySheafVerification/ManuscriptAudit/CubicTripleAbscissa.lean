import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-! The centered tripling equation has a root with nonzero division-polynomial denominator. -/

namespace ManuscriptAudit.CubicTripleAbscissa

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

def numerator (A x : K) : K :=
  x ^ 9 - 96 * A * x ^ 6 + 48 * A ^ 2 * x ^ 3 + 64 * A ^ 3

def denominator (A x : K) : K := 9 * x ^ 2 * (x ^ 3 + 4 * A) ^ 2

def triplingPolynomial (A u : K) : K[X] :=
  X ^ 9 + ((-(C (96 * A) * X ^ 6) + (C (48 * A ^ 2) * X ^ 3 + C (64 * A ^ 3))) -
    C (u * 9) * (X ^ 2 * (X ^ 3 + C (4 * A)) ^ 2))

theorem triplingPolynomial_degree (A u : K) : (triplingPolynomial A u).natDegree = 9 := by
  have h₁ : (-(C (96 * A) * (X : K[X]) ^ 6)).natDegree ≤ 6 := by
    rw [natDegree_neg]
    exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 6)
  have h₂ : (C (48 * A ^ 2) * (X : K[X]) ^ 3 + C (64 * A ^ 3)).natDegree ≤ 3 := by
    simpa only [natDegree_add_C] using
      (natDegree_C_mul_le (48 * A ^ 2) ((X : K[X]) ^ 3)).trans (natDegree_X_pow_le 3)
  have hnum : (-(C (96 * A) * (X : K[X]) ^ 6) +
      (C (48 * A ^ 2) * X ^ 3 + C (64 * A ^ 3))).natDegree ≤ 8 :=
    natDegree_add_le_of_degree_le (h₁.trans (by decide)) (h₂.trans (by decide))
  have hden : (C (u * 9) * ((X : K[X]) ^ 2 * (X ^ 3 + C (4 * A)) ^ 2)).natDegree ≤ 8 := by
    have hpow : (((X : K[X]) ^ 3 + C (4 * A)) ^ 2).natDegree ≤ 6 := by
      calc
        _ ≤ 2 * ((X : K[X]) ^ 3 + C (4 * A)).natDegree := natDegree_pow_le
        _ = 6 := by rw [natDegree_X_pow_add_C]
    exact (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le 2) hpow))
  have htail : (-(C (96 * A) * (X : K[X]) ^ 6) +
      (C (48 * A ^ 2) * X ^ 3 + C (64 * A ^ 3)) -
      C (u * 9) * (X ^ 2 * (X ^ 3 + C (4 * A)) ^ 2)).natDegree ≤ 8 := by
    rw [sub_eq_add_neg]
    exact natDegree_add_le_of_degree_le hnum (by simpa only [natDegree_neg] using hden)
  have htop : (8 : ℕ) < ((X : K[X]) ^ 9).natDegree := by
    rw [natDegree_X_pow]
    decide
  have hlt := htail.trans_lt htop
  rw [triplingPolynomial, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

theorem eval_triplingPolynomial (A u x : K) :
    (triplingPolynomial A u).eval x = numerator A x - u * denominator A x := by
  simp only [triplingPolynomial, numerator, denominator, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_X, eval_C]
  ring

/-- The numerator does not vanish at a zero of the centered tripling denominator. -/
theorem numerator_ne_of_denominator_zero {A x : K} (h₂ : (2 : K) ≠ 0)
    (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (h : denominator A x = 0) :
    numerator A x ≠ 0 := by
  have h₉ : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 ^ 2 by ring]
    exact pow_ne_zero _ h₃
  by_cases hx : x = 0
  · rw [hx]
    have he : numerator A (0 : K) = 2 ^ 6 * A ^ 3 := by unfold numerator; ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ hA)
  have hg : x ^ 3 + 4 * A = 0 := by
    unfold denominator at h
    by_contra hn
    exact mul_ne_zero (mul_ne_zero h₉ (pow_ne_zero _ hx)) (pow_ne_zero _ hn) h
  have hx3 : x ^ 3 = -(4 * A) := eq_neg_of_add_eq_zero_left hg
  have he : numerator A x = (-(12 : K)) ^ 3 * A ^ 3 := by
    unfold numerator
    rw [show x ^ 9 = (x ^ 3) ^ 3 by ring, show x ^ 6 = (x ^ 3) ^ 2 by ring, hx3]
    ring
  have h₁₂ : (12 : K) ≠ 0 := by
    rw [show (12 : K) = 3 * 2 ^ 2 by ring]
    exact mul_ne_zero h₃ (pow_ne_zero _ h₂)
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr h₁₂)) (pow_ne_zero _ hA)

/-- Every target abscissa admits a root with a nonzero tripling denominator. -/
theorem exists_triple_abscissa [IsAlgClosed K] {A : K} (h₂ : (2 : K) ≠ 0)
    (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (u : K) :
    ∃ x : K, denominator A x ≠ 0 ∧ numerator A x = u * denominator A x := by
  have hd := triplingPolynomial_degree A u
  have hne : triplingPolynomial A u ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hd
    omega
  have hdeg : (triplingPolynomial A u).degree ≠ 0 := by
    rw [degree_eq_natDegree hne, hd]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (triplingPolynomial A u) hdeg
  have he : numerator A x = u * denominator A x :=
    sub_eq_zero.mp ((eval_triplingPolynomial A u x).symm.trans hx)
  refine ⟨x, ?_, he⟩
  intro hz
  exact numerator_ne_of_denominator_zero h₂ h₃ hA hz (by rw [he, hz, mul_zero])

end
end ManuscriptAudit.CubicTripleAbscissa

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTripleAbscissa.triplingPolynomial_degree,
      ``ManuscriptAudit.CubicTripleAbscissa.eval_triplingPolynomial,
      ``ManuscriptAudit.CubicTripleAbscissa.numerator_ne_of_denominator_zero,
      ``ManuscriptAudit.CubicTripleAbscissa.exists_triple_abscissa] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
