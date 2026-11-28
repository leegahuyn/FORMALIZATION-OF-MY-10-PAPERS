import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspActualMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCuspFloquetPhase
import Mathlib.Tactic.FinCases

/-! Exact real scaling matrix, normalized modulus, and frequency convention at the odd level-four cusp pair. -/

namespace ManuscriptAudit.Paper8OddCrossScaledRows

open Matrix UpperHalfPlane
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspPhase Paper8OddCrossCuspCutoff
open Paper8OddCrossCuspActualMultiplier
open scoped MatrixGroups

noncomputable section

def realDiagonalWidthFour : SL(2, ℝ) :=
  ⟨!![2, 0; 0, (1 / 2 : ℝ)], by norm_num [Matrix.det_fin_two]⟩

def scaledCrossMatrix {D : ℕ} (A : CrossRow D) : SL(2, ℝ) :=
  ⟨!![2 * (A.matrix 0 0 : ℝ), (A.matrix 0 1 : ℝ) / 2;
      2 * (A.matrix 1 0 : ℝ), (A.matrix 1 1 : ℝ) / 2], by
    have hDet : A.matrix 0 0 * A.matrix 1 1 - A.matrix 0 1 * A.matrix 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe A.matrix
    have hR : (A.matrix 0 0 : ℝ) * (A.matrix 1 1 : ℝ) -
        (A.matrix 0 1 : ℝ) * (A.matrix 1 0 : ℝ) = 1 := by exact_mod_cast hDet
    simp only [Matrix.det_fin_two]
    change 2 * (A.matrix 0 0 : ℝ) * ((A.matrix 1 1 : ℝ) / 2) -
      (A.matrix 0 1 : ℝ) / 2 * (2 * (A.matrix 1 0 : ℝ)) = 1
    linear_combination hR⟩

theorem scaledCrossMatrix_as_product {D : ℕ} (A : CrossRow D) :
    (scaledCrossMatrix A : Matrix (Fin 2) (Fin 2) ℝ) =
      A.matrix.1.map (Int.castRingHom ℝ) * (realDiagonalWidthFour : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledCrossMatrix, realDiagonalWidthFour, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem scaledCrossMatrix_lowerLeft {D : ℕ} (A : CrossRow D) :
    scaledCrossMatrix A 1 0 = 2 * (D : ℝ) := by
  change 2 * (A.matrix 1 0 : ℝ) = 2 * (D : ℝ)
  rw [A.lowerLeft, Int.cast_natCast]

def oddInfinityFrequency : ℝ := 1 / 24

def oddZeroFrequency : ℝ := 1 / 6

def negativeWeightDiagonal (A : SL(2, ℝ)) : ℝ :=
  (oddInfinityFrequency * A 0 0 + oddZeroFrequency * A 1 1) / A 1 0

theorem scaledCrossMatrix_diagonal {D : ℕ} (A : CrossRow D) :
    negativeWeightDiagonal (scaledCrossMatrix A) =
      scaledCrossDiagonal D (A.matrix 0 0) (A.matrix 1 1) := by
  unfold negativeWeightDiagonal oddInfinityFrequency oddZeroFrequency scaledCrossDiagonal
  rw [scaledCrossMatrix_lowerLeft]
  change (((1 / 24 : ℝ) * (2 * (A.matrix 0 0 : ℝ)) +
    (1 / 6 : ℝ) * ((A.matrix 1 1 : ℝ) / 2)) / (2 * (D : ℝ))) = _
  ring

theorem crossRaw_normalized_modulus (j : ℕ) :
    crossRaw j = 2 * (crossSum (Nat.succ_pos j) / (2 * ((j + 1 : ℕ) : ℂ))) := by
  unfold crossRaw
  have hD : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp [hD] <;> ring

end
end ManuscriptAudit.Paper8OddCrossScaledRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossScaledRows.scaledCrossMatrix_as_product,
      ``ManuscriptAudit.Paper8OddCrossScaledRows.scaledCrossMatrix_diagonal,
      ``ManuscriptAudit.Paper8OddCrossScaledRows.crossRaw_normalized_modulus] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
