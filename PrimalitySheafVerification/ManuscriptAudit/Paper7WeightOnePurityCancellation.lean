import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PrimalitySheafVerification.ManuscriptAudit.Paper7NonvacuousPurityCancellation

/-! The scalar local condition misses a canceled eigenvalue at the manuscript's weight one. -/

namespace ManuscriptAudit.Paper7WeightOnePurityCancellation

open Matrix Polynomial Paper7NonvacuousPurityCancellation

noncomputable section

def root (p : ℕ) : ℂ := (Real.sqrt (p : ℝ) : ℂ)

def evenDeterminant (p : ℕ) : ℂ[X] :=
  (Matrix.diagonal ![factor (root p), factor 1]).det

def combinedFactor (p : ℕ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) degreeOneMatrix.det /
    algebraMap ℂ[X] (RatFunc ℂ) (evenDeterminant p)

private theorem mapped_factor_nonzero (z : ℂ) :
    algebraMap ℂ[X] (RatFunc ℂ) (factor z) ≠ 0 := by
  intro hz
  have he : factor z = 0 := (RatFunc.algebraMap_injective ℂ) (hz.trans (map_zero _).symm)
  have h := congrArg (Polynomial.eval 0) he
  norm_num [factor] at h

theorem literal_cancellation (p : ℕ) :
    combinedFactor p = (algebraMap ℂ[X] (RatFunc ℂ) (factor (root p)))⁻¹ := by
  have hZero : evenDeterminant p = factor (root p) * factor 1 := by
    simp [evenDeterminant, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [combinedFactor, hZero, degreeOne_det, map_mul]
  field_simp [mapped_factor_nonzero 1, mapped_factor_nonzero (root p)] <;> ring

theorem weight_one_invisible_eigenvalue (p : ℕ) (hp : 1 < p) :
    (factor (root p)).IsRoot ((root p)⁻¹) ∧
      ‖(root p)⁻¹‖ = (Real.sqrt (p : ℝ))⁻¹ ∧
      (factor 1).IsRoot 1 ∧ ‖(1 : ℂ)‖ ≠ Real.sqrt (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (zero_lt_one.trans hpR)
  have hRoot : root p ≠ 0 := by
    unfold root
    exact_mod_cast hPos.ne'
  refine ⟨?_, ?_, by simp [Polynomial.IsRoot, factor], ?_⟩
  · change (factor (root p)).eval ((root p)⁻¹) = 0
    simp [factor, mul_inv_cancel₀ hRoot]
  · rw [norm_inv, root, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPos]
  · rw [norm_one]
    intro h
    have hSq := Real.sq_sqrt (show (0 : ℝ) ≤ p from by positivity)
    rw [← h] at hSq
    norm_num at hSq
    exact hpR.ne hSq

end
end ManuscriptAudit.Paper7WeightOnePurityCancellation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7WeightOnePurityCancellation.literal_cancellation,
      ``ManuscriptAudit.Paper7WeightOnePurityCancellation.weight_one_invisible_eigenvalue] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
