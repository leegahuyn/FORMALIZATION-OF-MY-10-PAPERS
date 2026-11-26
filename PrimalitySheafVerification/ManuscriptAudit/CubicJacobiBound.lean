import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount
import PrimalitySheafVerification.ManuscriptAudit.JacobiComplexNorm

/-! The exact cubic trace reduction to two Jacobi sums. -/

namespace ManuscriptAudit.CubicJacobiBound

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def quadraticComplex : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem quadraticComplex_shift_sum (hF : ringChar F ≠ 2) (A : F) :
    (∑ z : F, quadraticComplex (z + A)) = 0 := by
  let e : F ≃ F :=
    { toFun := fun z => z + A, invFun := fun z => z - A
      left_inv := fun z => add_sub_cancel_right z A
      right_inv := fun z => sub_add_cancel z A }
  change (∑ z : F, quadraticComplex (e z)) = 0
  rw [Equiv.sum_comp e]
  change (∑ z : F, (quadraticChar F z : ℂ)) = 0
  rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]

def cubicTraceSum (A : F) : ℂ := ∑ x : F, quadraticComplex (x ^ 3 + A)

abbrev cubeMultiplicity (z : F) := Fintype.card {x : F // x ^ 3 = z}

/-- Collecting equal cubes and shifting the quadratic character gives the two sums term by term. -/
theorem cubicTraceSum_eq (hF : ringChar F ≠ 2) (ψ : MulChar F ℂ) {A : F} (hA : A ≠ 0)
    (hroot : ∀ z : F, (cubeMultiplicity z : ℂ) = 1 + ψ z + (ψ ^ 2) z) :
    cubicTraceSum A =
      ψ (-A) * quadraticComplex A * jacobiSum ψ quadraticComplex +
      (ψ ^ 2) (-A) * quadraticComplex A * jacobiSum (ψ ^ 2) quadraticComplex := by
  have hσ :
      (∑ z : F, (∑ _x : {x : F // x ^ 3 = z}, quadraticComplex (z + A))) =
        cubicTraceSum A :=
    Fintype.sum_fiberwise' (fun x : F => x ^ 3) (fun z : F => quadraticComplex (z + A))
  rw [← hσ]
  have hterm (z : F) :
      (∑ _x : {x : F // x ^ 3 = z}, quadraticComplex (z + A)) =
        (1 + ψ z + (ψ ^ 2) z) * quadraticComplex (z + A) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hroot z]
  simp_rw [hterm, add_mul, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, quadraticComplex_shift_sum hF, zero_add]
  rw [JacobiComplexNorm.shifted_sum_eq_jacobi ψ quadraticComplex hA,
    JacobiComplexNorm.shifted_sum_eq_jacobi (ψ ^ 2) quadraticComplex hA]

/-- A point-count Hasse bound as soon as the actual cubic character multiplicity is identified. -/
theorem cubicTraceSum_norm_le (hF : ringChar F ≠ 2) (hchar : ringChar ℂ ≠ ringChar F)
    (ψ : MulChar F ℂ) {A : F} (hA : A ≠ 0)
    (hroot : ∀ z : F, (cubeMultiplicity z : ℂ) = 1 + ψ z + (ψ ^ 2) z)
    (hψ : ψ ≠ 1) (hψ₂ : ψ ^ 2 ≠ 1)
    (hφ : (quadraticComplex : MulChar F ℂ) ≠ 1)
    (hψφ : ψ * quadraticComplex ≠ 1) (hψ₂φ : (ψ ^ 2) * quadraticComplex ≠ 1) :
    ‖cubicTraceSum A‖ ≤ 2 * Real.sqrt (Fintype.card F : ℝ) := by
  rw [cubicTraceSum_eq hF ψ hA hroot]
  rw [← JacobiComplexNorm.shifted_sum_eq_jacobi ψ quadraticComplex hA,
    ← JacobiComplexNorm.shifted_sum_eq_jacobi (ψ ^ 2) quadraticComplex hA]
  refine (norm_add_le _ _).trans ?_
  rw [JacobiComplexNorm.norm_shifted_sum hchar hψ hφ hψφ hA,
    JacobiComplexNorm.norm_shifted_sum hchar hψ₂ hφ hψ₂φ hA]
  linarith

theorem pointTrace_norm_eq (hF : ringChar F ≠ 2) {A : F}
    (hΔ : (FiniteFieldPointCount.shortCubic (0 : F) A).Δ ≠ 0) :
    |(Fintype.card F : ℝ) + 1 -
      (Nat.card (FiniteFieldPointCount.shortCubic (0 : F) A).toProjective.Point : ℝ)| =
      ‖cubicTraceSum A‖ := by
  have hc := FiniteFieldPointCount.shortCubic_projective_count_int hF hΔ
  simp only [zero_mul, sub_zero] at hc
  change |(Fintype.card F : ℝ) + 1 -
      (Nat.card (FiniteFieldPointCount.shortCubic (0 : F) A).toProjective.Point : ℝ)| =
    ‖∑ x : F, (quadraticChar F (x ^ 3 + A) : ℂ)‖
  rw [← Int.cast_sum, Complex.norm_intCast]
  have he := congrArg (fun x : ℤ => (x : ℝ)) hc
  push_cast at he
  rw [he]
  have hs : (Fintype.card F : ℝ) + 1 -
      ((Fintype.card F : ℝ) + 1 + ∑ x : F, (quadraticChar F (x ^ 3 + A) : ℝ)) =
      -(∑ x : F, (quadraticChar F (x ^ 3 + A) : ℝ)) := by ring
  rw [hs, abs_neg, Int.cast_sum]

end
end ManuscriptAudit.CubicJacobiBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicJacobiBound.cubicTraceSum_eq,
      ``ManuscriptAudit.CubicJacobiBound.cubicTraceSum_norm_le,
      ``ManuscriptAudit.CubicJacobiBound.pointTrace_norm_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
