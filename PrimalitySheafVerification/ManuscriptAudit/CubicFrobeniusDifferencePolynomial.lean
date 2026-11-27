import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Derivative
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceNumerator

/-! Polynomial degrees and local cancellation for the relative Frobenius difference. -/

namespace ManuscriptAudit.CubicFrobeniusDifferencePolynomial

open Polynomial CubicFrobeniusDifferenceNumerator

variable {K : Type*} [Field K]

/-- The numerator's leading degree before reduction is 2q+1. -/
theorem numerator_natDegree {q k : ℕ} (hq : q = 2 * k + 1) (hk : 0 < k) (A : K) :
    (numerator q k A).natDegree = 2 * q + 1 := by
  let D : K[X] := X ^ 3 + C A
  let P : K[X] := X ^ (q + 2) + C (2 * A)
  let Q : K[X] := C 2 * D ^ (k + 1)
  have hD : D.natDegree = 3 := by simp [D, natDegree_X_pow]
  have hP : P.natDegree = q + 2 := by simp [P, natDegree_X_pow]
  have hQ : Q.natDegree ≤ (k + 1) * 3 := by
    calc
      _ ≤ (C (2 : K)).natDegree + (D ^ (k + 1)).natDegree := by apply natDegree_mul_le
      _ = _ := by rw [natDegree_C, zero_add, natDegree_pow, hD]
  have hPQ : (P + Q).natDegree ≤ max (q + 2) ((k + 1) * 3) := by
    calc
      _ ≤ max P.natDegree Q.natDegree := by apply natDegree_add_le
      _ ≤ _ := max_le_max hP.le hQ
  have hlt : (P + Q).natDegree < ((X : K[X]) ^ (2 * q + 1)).natDegree := by
    rw [natDegree_X_pow]
    exact hPQ.trans_lt (max_lt_iff.mpr ⟨by omega, by omega⟩)
  have hEq : numerator q k A = X ^ (2 * q + 1) + (P + Q) := by
    simp only [numerator, P, Q, D, add_assoc]
  rw [hEq, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

/-- A root contributes a square factor exactly when the derivative vanishes there too. -/
theorem square_linear_dvd_iff {f : K[X]} {x : K} :
    (X - C x) ^ 2 ∣ f ↔ f.IsRoot x ∧ f.derivative.IsRoot x := by
  constructor
  · rintro ⟨g, rfl⟩
    constructor
    · simp [IsRoot]
    · simp [IsRoot, derivative_mul, derivative_X_sub_C_sq]
  · rintro ⟨hf, hDer⟩
    obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hf
    have hEval : f.derivative.eval x = g.eval x := by
      rw [hg, derivative_mul, derivative_X_sub_C]
      simp
    have hgRoot : g.IsRoot x := hEval.symm.trans hDer
    obtain ⟨u, hu⟩ := dvd_iff_isRoot.mpr hgRoot
    exact ⟨u, by rw [hg, hu, pow_two, mul_assoc]⟩

variable (K) [Fintype K]

/-- The polynomial for the rational abscissas has constant derivative −1. -/
theorem denominator_base_derivative :
    (((X : K[X]) ^ Fintype.card K) - X).derivative = -1 := by
  rw [derivative_sub, derivative_X_pow, derivative_X, FiniteField.cast_card_eq_zero K,
    C_0, zero_mul, zero_sub]

end ManuscriptAudit.CubicFrobeniusDifferencePolynomial

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusDifferencePolynomial.numerator_natDegree,
      ``ManuscriptAudit.CubicFrobeniusDifferencePolynomial.square_linear_dvd_iff,
      ``ManuscriptAudit.CubicFrobeniusDifferencePolynomial.denominator_base_derivative] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
