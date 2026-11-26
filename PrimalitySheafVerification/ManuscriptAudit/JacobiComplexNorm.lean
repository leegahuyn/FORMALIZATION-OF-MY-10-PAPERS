import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Magnitudes of actual complex Jacobi character sums over a finite field. -/

namespace ManuscriptAudit.JacobiComplexNorm

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem character_norm_one (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    ‖χ a‖ = 1 := by
  have he := congrArg (fun x : F => χ x) (FiniteField.pow_card_sub_one_eq_one a ha)
  rw [map_pow, map_one] at he
  have hq : Fintype.card F - 1 ≠ 0 := by
    have hc : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  exact Complex.norm_eq_one_of_pow_eq_one he hq

theorem invCharacter_eq_conj (χ : MulChar F ℂ) (a : F) :
    χ⁻¹ a = (starRingEnd ℂ) (χ a) := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : a = 0
  · subst a
    simp
  · exact Complex.inv_eq_conj (character_norm_one χ ha)

theorem jacobiSum_inv_eq_conj (χ ψ : MulChar F ℂ) :
    jacobiSum χ⁻¹ ψ⁻¹ = (starRingEnd ℂ) (jacobiSum χ ψ) := by
  unfold jacobiSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, invCharacter_eq_conj, invCharacter_eq_conj]

/-- The exact square-root size for the actual Jacobi sum of nontrivial characters. -/
theorem norm_jacobiSum (hchar : ringChar ℂ ≠ ringChar F)
    {χ ψ : MulChar F ℂ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have h := jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ
  rw [jacobiSum_inv_eq_conj] at h
  have he : (↑(‖jacobiSum χ ψ‖ ^ 2) : ℂ) = (Fintype.card F : ℂ) :=
    (Complex.mul_conj' (jacobiSum χ ψ)).symm.trans h
  have he' : ‖jacobiSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by exact_mod_cast he
  rw [← he', Real.sqrt_sq (norm_nonneg _)]

/-- The native shifted multiplicative sum is an exact scaled Jacobi sum. -/
theorem shifted_sum_eq_jacobi (χ ψ : MulChar F ℂ) {A : F} (hA : A ≠ 0) :
    (∑ a : F, χ a * ψ (a + A)) = χ (-A) * ψ A * jacobiSum χ ψ := by
  classical
  have hn : -A ≠ 0 := neg_ne_zero.mpr hA
  let e : F ≃ F :=
    { toFun := fun x => (-A) * x
      invFun := fun x => (-A)⁻¹ * x
      left_inv := fun x => by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
      right_inv := fun x => by rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] }
  calc
    _ = ∑ a : F, χ ((-A) * a) * ψ ((-A) * a + A) :=
      (Equiv.sum_comp e (fun a : F => χ a * ψ (a + A))).symm
    _ = _ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have h : (-A) * a + A = A * (1 - a) := by ring
      rw [h, map_mul, map_mul]
      ring

theorem norm_shifted_sum (hchar : ringChar ℂ ≠ ringChar F)
    {χ ψ : MulChar F ℂ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {A : F} (hA : A ≠ 0) :
    ‖∑ a : F, χ a * ψ (a + A)‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [shifted_sum_eq_jacobi χ ψ hA, norm_mul, norm_mul,
    character_norm_one χ (neg_ne_zero.mpr hA), character_norm_one ψ hA,
    one_mul, one_mul, norm_jacobiSum hchar hχ hψ hχψ]

end
end ManuscriptAudit.JacobiComplexNorm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.JacobiComplexNorm.character_norm_one,
      ``ManuscriptAudit.JacobiComplexNorm.jacobiSum_inv_eq_conj,
      ``ManuscriptAudit.JacobiComplexNorm.norm_jacobiSum,
      ``ManuscriptAudit.JacobiComplexNorm.shifted_sum_eq_jacobi,
      ``ManuscriptAudit.JacobiComplexNorm.norm_shifted_sum] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
