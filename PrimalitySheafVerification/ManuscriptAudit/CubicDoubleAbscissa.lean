import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-! The centered doubling quartic has a root away from the vanishing denominator. -/

namespace ManuscriptAudit.CubicDoubleAbscissa

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

def doublingQuartic (A u : K) : K[X] :=
  X ^ 4 + (-(C (4 * u) * X ^ 3) + (-(C (8 * A) * X) + C (-(4 * u * A))))

theorem doublingQuartic_degree (A u : K) : (doublingQuartic A u).natDegree = 4 := by
  have h₁ : (-(C (4 * u) * (X : K[X]) ^ 3)).natDegree ≤ 3 := by
    rw [natDegree_neg]
    exact (natDegree_C_mul_le (4 * u) ((X : K[X]) ^ 3)).trans (natDegree_X_pow_le 3)
  have h₂ : (-(C (8 * A) * (X : K[X])) + C (-(4 * u * A))).natDegree ≤ 1 := by
    simpa only [natDegree_add_C, natDegree_neg, natDegree_X] using
      natDegree_C_mul_le (8 * A) (X : K[X])
  have htail : (-(C (4 * u) * (X : K[X]) ^ 3) +
      (-(C (8 * A) * X) + C (-(4 * u * A)))).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le h₁ (h₂.trans (by decide))
  have hlt : (-(C (4 * u) * (X : K[X]) ^ 3) +
      (-(C (8 * A) * X) + C (-(4 * u * A)))).natDegree < ((X : K[X]) ^ 4).natDegree := by
    rw [natDegree_X_pow]
    omega
  rw [doublingQuartic, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

theorem eval_doublingQuartic (A u x : K) :
    (doublingQuartic A u).eval x = x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) := by
  simp only [doublingQuartic, eval_add, eval_neg, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-- Every target abscissa has a root of the doubling equation with a nonzero ordinate square. -/
theorem exists_double_abscissa [IsAlgClosed K] {A : K} (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (u : K) : ∃ x : K, x ^ 3 + A ≠ 0 ∧ x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) = 0 := by
  have hd := doublingQuartic_degree A u
  have hne : doublingQuartic A u ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hd
    omega
  have hdeg : (doublingQuartic A u).degree ≠ 0 := by
    rw [degree_eq_natDegree hne, hd]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (doublingQuartic A u) hdeg
  have he : x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) = 0 :=
    (eval_doublingQuartic A u x).symm.trans hx
  refine ⟨x, ?_, he⟩
  intro hzero
  have hCube : x ^ 3 = -A := eq_neg_of_add_eq_zero_left hzero
  have hx₀ : x ≠ 0 := by
    intro h
    exact hA (by simpa [h] using hzero)
  have h₉ : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 ^ 2 by ring]
    exact pow_ne_zero _ h₃
  apply mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h₉) hA) hx₀
  calc
    -(9 : K) * A * x = x * x ^ 3 - 8 * A * x := by rw [hCube]; ring
    _ = x ^ 4 - 8 * A * x - 4 * u * (x ^ 3 + A) := by rw [hzero]; ring
    _ = 0 := he

end
end ManuscriptAudit.CubicDoubleAbscissa

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicDoubleAbscissa.doublingQuartic_degree,
      ``ManuscriptAudit.CubicDoubleAbscissa.eval_doublingQuartic,
      ``ManuscriptAudit.CubicDoubleAbscissa.exists_double_abscissa] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
