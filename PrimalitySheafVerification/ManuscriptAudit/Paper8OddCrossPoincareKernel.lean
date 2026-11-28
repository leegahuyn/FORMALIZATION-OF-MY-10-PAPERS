import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossScaledRows
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! The one-row Möbius phase separates into the actual cross-cusp coefficient and a modulus-only kernel. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareKernel

open Matrix MaassLaplacian Paper8OddCrossCuspNormalization Paper8OddCrossScaledRows
open Paper8OddCrossCuspPhase
open scoped MatrixGroups

noncomputable section

def matrixMoebius (g : SL(2, ℝ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) /
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))

private theorem denominator_nonzero (g : SL(2, ℝ)) {x y : ℝ}
    (hc : g 1 0 ≠ 0) (hy : 0 < y) :
    (g 1 0 : ℂ) * complexPoint x y + (g 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    complexPoint_im, mul_zero, zero_mul, add_zero, Complex.zero_im] at hi
  exact mul_ne_zero hc hy.ne' hi

theorem matrixMoebius_shift (g : SL(2, ℝ)) {x y : ℝ} (hc : g 1 0 ≠ 0) (hy : 0 < y) :
    matrixMoebius g (complexPoint x y) =
      (g 0 0 : ℂ) / (g 1 0 : ℂ) -
        1 / ((g 1 0 : ℂ) ^ 2 * complexPoint (x + g 1 1 / g 1 0) y) := by
  let a : ℂ := g 0 0
  let b : ℂ := g 0 1
  let c : ℂ := g 1 0
  let d : ℂ := g 1 1
  let z := complexPoint x y
  let w := complexPoint (x + g 1 1 / g 1 0) y
  have hC : c ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hD : c * z + d ≠ 0 := denominator_nonzero g hc hy
  have hDetR : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  have hDet : a * d - b * c = 1 := by
    change (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1
    exact_mod_cast hDetR
  have hProd : c * w = c * z + d := by
    unfold w z complexPoint
    push_cast
    change c * ((x : ℂ) + d / c + (y : ℂ) * Complex.I) =
      c * ((x : ℂ) + (y : ℂ) * Complex.I) + d
    field_simp [hC] <;> ring
  have hRepack : c ^ 2 * w = c * (c * z + d) := by rw [← hProd]; ring
  change (a * z + b) / (c * z + d) = a / c - 1 / (c ^ 2 * w)
  rw [hRepack]
  apply (div_eq_iff hD).2
  calc
    _ = (a * (c * z + d) - 1) / c := by
      apply (eq_div_iff hC).2
      linear_combination -hDet
    _ = _ := by field_simp [hC, hD] <;> ring

def exponentialPhase (z : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)

theorem row_exponential_phase (g : SL(2, ℝ)) {x y : ℝ} (hc : g 1 0 ≠ 0) (hy : 0 < y) (μ ν : ℝ) :
    exponentialPhase ((μ : ℂ) * matrixMoebius g (complexPoint x y) - (ν : ℂ) * (x : ℂ)) =
      exponentialPhase (((μ * g 0 0 + ν * g 1 1) / g 1 0 : ℝ) : ℂ) *
        exponentialPhase (-(μ : ℂ) /
          ((g 1 0 : ℂ) ^ 2 * complexPoint (x + g 1 1 / g 1 0) y) -
          (ν : ℂ) * ((x + g 1 1 / g 1 0 : ℝ) : ℂ)) := by
  rw [matrixMoebius_shift g hc hy]
  unfold exponentialPhase
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

theorem scaledCross_row_exponential_phase {D : ℕ} (hD : 0 < D) (A : CrossRow D)
    {x y : ℝ} (hy : 0 < y) :
    let g := scaledCrossMatrix A
    exponentialPhase ((oddInfinityFrequency : ℂ) * matrixMoebius g (complexPoint x y) -
      (oddZeroFrequency : ℂ) * (x : ℂ)) =
      exponentialPhase (scaledCrossDiagonal D (A.matrix 0 0) (A.matrix 1 1) : ℂ) *
        exponentialPhase (-(oddInfinityFrequency : ℂ) /
          ((g 1 0 : ℂ) ^ 2 * complexPoint (x + g 1 1 / g 1 0) y) -
          (oddZeroFrequency : ℂ) * ((x + g 1 1 / g 1 0 : ℝ) : ℂ)) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hc : scaledCrossMatrix A 1 0 ≠ 0 := by
    rw [scaledCrossMatrix_lowerLeft]
    exact mul_ne_zero (by norm_num) hD0
  have h := row_exponential_phase (scaledCrossMatrix A) (x := x) hc hy oddInfinityFrequency oddZeroFrequency
  dsimp only at h ⊢
  rw [show ((oddInfinityFrequency * (scaledCrossMatrix A) 0 0 +
      oddZeroFrequency * (scaledCrossMatrix A) 1 1) / (scaledCrossMatrix A) 1 0 : ℝ) =
        scaledCrossDiagonal D (A.matrix 0 0) (A.matrix 1 1) from scaledCrossMatrix_diagonal A] at h
  exact h

end
end ManuscriptAudit.Paper8OddCrossPoincareKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareKernel.scaledCross_row_exponential_phase
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
