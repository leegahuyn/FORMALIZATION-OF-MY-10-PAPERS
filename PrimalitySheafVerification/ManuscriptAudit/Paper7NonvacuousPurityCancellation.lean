import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A nonconstant local factor can hide degreewise impurity

Literal native determinants in degrees zero and one share a nontrivial
factor. After exact cancellation in the rational function field, the
remaining factor still has a genuine reciprocal root at the proposed
degree-zero radius.
-/

namespace ManuscriptAudit.Paper7NonvacuousPurityCancellation

open Polynomial Matrix

noncomputable section

def factor (a : ℂ) : ℂ[X] := 1 - C a * X

def degreeZeroMatrix (q : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  Matrix.diagonal ![factor (q : ℂ), factor 1]

def degreeOneMatrix : Matrix (Fin 1) (Fin 1) ℂ[X] :=
  Matrix.diagonal ![factor 1]

theorem degreeZero_det (q : ℕ) :
    (degreeZeroMatrix q).det = factor (q : ℂ) * factor 1 := by
  simp [degreeZeroMatrix, Matrix.det_diagonal, Fin.prod_univ_two]

theorem degreeOne_det : degreeOneMatrix.det = factor 1 := by
  simp [degreeOneMatrix, Matrix.det_diagonal, Fin.prod_univ_one]

private theorem factor_nonzero (a : ℂ) : factor a ≠ 0 := by
  intro h
  have e := congrArg (Polynomial.eval 0) h
  norm_num [factor] at e

def gradedFactor (q : ℕ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) degreeOneMatrix.det /
    algebraMap ℂ[X] (RatFunc ℂ) (degreeZeroMatrix q).det

theorem gradedFactor_eq (q : ℕ) :
    gradedFactor q = (algebraMap ℂ[X] (RatFunc ℂ) (factor (q : ℂ)))⁻¹ := by
  rw [gradedFactor, degreeZero_det, degreeOne_det, map_mul]
  have h : algebraMap ℂ[X] (RatFunc ℂ) (factor 1) ≠ 0 :=
    fun h => factor_nonzero 1 ((RatFunc.algebraMap_injective ℂ) (h.trans (map_zero _).symm))
  have hq : algebraMap ℂ[X] (RatFunc ℂ) (factor (q : ℂ)) ≠ 0 :=
    fun h => factor_nonzero (q : ℂ) ((RatFunc.algebraMap_injective ℂ) (h.trans (map_zero _).symm))
  field_simp [h, hq] <;> ring

theorem reducedFactor_root_iff (q : ℕ) (hq : 1 < q) (z : ℂ) :
    (factor (q : ℂ)).IsRoot z ↔ z = (q : ℂ)⁻¹ := by
  have hqn : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  change (factor (q : ℂ)).eval z = 0 ↔ _
  simp only [factor, eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero]
  constructor
  · intro hz
    rw [← one_div]
    apply (eq_div_iff hqn).mpr
    simpa only [mul_comm] using hz.symm
  · rintro rfl
    rw [mul_inv_cancel₀ hqn]

theorem reciprocal_radius_and_hidden_impurity (q : ℕ) (hq : 1 < q) :
    ((factor (q : ℂ)).IsRoot ((q : ℂ)⁻¹) ∧
      ‖(q : ℂ)⁻¹‖ = (q : ℝ)⁻¹) ∧
      (factor 1).IsRoot 1 ∧ ‖(1 : ℂ)‖ ≠ (q : ℝ) := by
  refine ⟨⟨(reducedFactor_root_iff q hq _).2 rfl, ?_⟩, ?_, ?_⟩
  · simp
  · simp [Polynomial.IsRoot, factor]
  · have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    simpa only [norm_one] using hqR.ne

end
end ManuscriptAudit.Paper7NonvacuousPurityCancellation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7NonvacuousPurityCancellation.degreeZero_det,
      ``ManuscriptAudit.Paper7NonvacuousPurityCancellation.degreeOne_det,
      ``ManuscriptAudit.Paper7NonvacuousPurityCancellation.gradedFactor_eq,
      ``ManuscriptAudit.Paper7NonvacuousPurityCancellation.reducedFactor_root_iff,
      ``ManuscriptAudit.Paper7NonvacuousPurityCancellation.reciprocal_radius_and_hidden_impurity] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
