import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! A multiplicative nondegenerate quadratic degree gives the endomorphism's arithmetic quadratic relation. -/

namespace ManuscriptAudit.QuadraticDegreeRelation

variable {R : Type*} [Ring R]

/-- The degree form gives the quadratic relation using the degree of f and of f−1. -/
theorem quadratic_relation (D : QuadraticMap ℤ R ℤ) (hOne : D 1 = 1)
    (hMul : ∀ x y : R, D (x * y) = D x * D y) (hZero : ∀ x : R, D x = 0 → x = 0)
    (f : R) :
    let q := D f
    let t := q + 1 - D (f - 1)
    f ^ 2 - t • f + q • (1 : R) = 0 := by
  let P := QuadraticMap.polar D
  let q := D f
  let t := P f 1
  have hAdd (x y : R) : D (x + y) = D x + D y + P x y := by
    dsimp only [P, QuadraticMap.polar]
    ring
  have hAdd₃ (x y z : R) :
      D (x + y + z) = D x + D y + D z + P x y + P x z + P y z := by
    rw [hAdd (x + y) z, hAdd x y]
    have hp : P (x + y) z = P x z + P y z := QuadraticMap.polar_add_left D x y z
    rw [hp]
    ring
  have hScale (a : ℤ) (x : R) : D (a • x) = a ^ 2 * D x := by
    simpa [zsmul_eq_mul, pow_two] using D.map_smul a x
  have hPL (a : ℤ) (x y : R) : P (a • x) y = a * P x y := by
    simpa [zsmul_eq_mul, P] using QuadraticMap.polar_smul_left D a x y
  have hPR (a : ℤ) (x y : R) : P x (a • y) = a * P x y := by
    simpa [zsmul_eq_mul, P] using QuadraticMap.polar_smul_right D a x y
  have hMP (x y : R) : P (f * x) (f * y) = q * P x y := by
    change D (f * x + f * y) - D (f * x) - D (f * y) =
      D f * (D (x + y) - D x - D y)
    rw [← mul_add, hMul, hMul, hMul]
    ring
  have hF₂ : D (f ^ 2) = q ^ 2 := by
    simpa only [pow_two, q] using hMul f f
  have hP₂ : P (f ^ 2) f = q * t := by
    simpa only [pow_two, mul_one, t] using hMP f (1 : R)
  have hF₁ : D (f + 1) = q + 1 + t := by
    rw [hAdd f 1, hOne]
  have hSq : (f + 1) ^ 2 = f ^ 2 + (2 : ℤ) • f + 1 := by
    rw [two_smul ℤ]
    noncomm_ring
  have hSquare :
      (q + 1 + t) ^ 2 = q ^ 2 + 4 * q + 1 + 2 * q * t + P (f ^ 2) 1 + 2 * t := by
    calc
      _ = D ((f + 1) ^ 2) := by rw [pow_two (f + 1), hMul, hF₁, pow_two]
      _ = D (f ^ 2 + (2 : ℤ) • f + 1) := congrArg D hSq
      _ = _ := by
        simp only [hAdd₃, hF₂, hScale, hOne, hPL, hPR, hP₂]
        dsimp only [q, t]
        ring
  have hP₁ : P (f ^ 2) 1 = t ^ 2 - 2 * q := by nlinarith only [hSquare]
  let F := f ^ 2 + (-t) • f + q • (1 : R)
  have hF : D F = 0 := by
    change D (f ^ 2 + (-t) • f + q • (1 : R)) = 0
    simp only [hAdd₃, hF₂, hScale, hOne, hPL, hPR, hP₂, hP₁]
    dsimp only [q, t]
    ring
  have hT : q + 1 - D (f - 1) = t := by
    have hN : P f (-1) = -t := QuadraticMap.polar_neg_right D f 1
    rw [sub_eq_add_neg f 1, hAdd, D.map_neg, hOne, hN]
    dsimp only [q]
    ring
  dsimp only
  rw [show D f + 1 - D (f - 1) = t from hT]
  simpa only [F, sub_eq_add_neg, neg_zsmul] using hZero F hF

end ManuscriptAudit.QuadraticDegreeRelation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.QuadraticDegreeRelation.quadratic_relation
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
