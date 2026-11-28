import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareTranslate

/-! The exact cross-cusp Fourier integrand is arithmetic coefficient times a common real-line kernel. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareRowKernel

open UpperHalfPlane MaassLaplacian Paper8ActualEtaSquaredModularity
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspActualMultiplier Paper8OddCrossCuspPhase
open Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareHeight
open Paper8OddCrossPoincareKernel Paper8OddCrossScaledRows Paper8OddCrossPoincareTranslate
open Paper8EtaPhaseCocycle
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

noncomputable section

def normalizedNegativeRoot (w : ℂ) : ℂ :=
  (Complex.sqrt w / (Real.sqrt ‖w‖ : ℂ)) * ((‖w‖ : ℂ) / w)

private theorem normalizedNegativeRoot_scale {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    normalizedNegativeRoot ((r : ℂ) * w) = normalizedNegativeRoot w := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hSr : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hr).ne'
  have hSw : (Real.sqrt ‖w‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (norm_pos_iff.mpr hw)).ne'
  have hReal : Complex.sqrt (r : ℂ) = (Real.sqrt r : ℂ) := by
    rw [sqrt_eq_exp hrC, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_log hr.le]
    congr 1
    push_cast
    ring
  have hMul : Complex.sqrt ((r : ℂ) * w) = (Real.sqrt r : ℂ) * Complex.sqrt w := by
    rw [← hReal, sqrt_eq_exp (mul_ne_zero hrC hw), sqrt_eq_exp hrC, sqrt_eq_exp hw,
      Complex.log_ofReal_mul hr hw, ← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_log hr.le]
    ring
  unfold normalizedNegativeRoot
  rw [hMul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Real.sqrt_mul hr.le]
  push_cast
  field_simp [hrC, hSr, hSw, hw] <;> ring

theorem normalizedNegativeRoot_norm {w : ℂ} (hw : w ≠ 0) :
    ‖normalizedNegativeRoot w‖ = 1 := by
  have hW : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hS : ‖Complex.sqrt w‖ = Real.sqrt ‖w‖ := by
    rw [sqrt_eq_exp hw, Complex.norm_exp, Complex.div_ofNat_re, Complex.log_re,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hW]
    congr 1
    ring
  have hReal : 0 < Real.sqrt ‖w‖ := Real.sqrt_pos.2 hW
  unfold normalizedNegativeRoot
  rw [norm_mul, norm_div, norm_div, hS, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hReal, abs_of_pos hW,
    div_self hReal.ne', div_self hW.ne', mul_one]

def crossRealKernel (s : ℂ) (y c u : ℝ) : ℂ :=
  let w := complexPoint u y
  (starRingEnd ℂ) (normalizedNegativeRoot w) *
    ((y / (c ^ 2 * (u ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ s *
    exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * w) -
      (oddZeroFrequency : ℂ) * (u : ℂ))

theorem oddCrossFourierTerm_row_kernel {D : ℕ} (A : CrossRow (D + 1)) (s : ℂ) (z : ℍ) :
    oddCrossFourierTerm s z ⟨D, A, 0⟩ =
      crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
        crossRealKernel s z.im (2 * ((D + 1 : ℕ) : ℝ)) (z.re + crossRowShift A) := by
  let g : SL(2, ℝ) := scaledCrossMatrix A
  let q : ℍ := realDiagonalWidthFour • z
  let c : ℝ := 2 * ((D + 1 : ℕ) : ℝ)
  let u : ℝ := z.re + crossRowShift A
  let w : ℂ := complexPoint u z.im
  have hD : 0 < D + 1 := Nat.succ_pos D
  have hP : 0 < ((D + 1 : ℕ) : ℝ) := by exact_mod_cast hD
  have hw : w ≠ 0 := by
    intro h
    have hIm := congrArg Complex.im h
    change (complexPoint u z.im).im = 0 at hIm
    rw [complexPoint_im] at hIm
    exact z.im_ne_zero hIm
  have hShift : crossRowShift A = (A.matrix 1 1 : ℝ) / (4 * ((D + 1 : ℕ) : ℝ)) := by
    unfold crossRowShift
    rw [scaledCrossMatrix_lowerLeft]
    change (A.matrix 1 1 : ℝ) / 2 / (2 * ((D + 1 : ℕ) : ℝ)) = _
    field_simp [hP.ne'] <;> ring
  have hPoint : complexPoint z.re z.im = (z : ℂ) := Complex.re_add_im z
  have hDen : denominator A.matrix q = ((4 * ((D + 1 : ℕ) : ℝ) : ℝ) : ℂ) * w := by
    unfold denominator
    rw [show (q : ℂ) = 4 * (z : ℂ) from realDiagonalWidthFour_smul_coe z,
      A.lowerLeft, Int.cast_natCast, ← hPoint]
    dsimp only [w, u]
    rw [hShift]
    unfold complexPoint
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hP.ne'] <;> ring
  have hGeom : negativeSquareRootPhase A.matrix q = normalizedNegativeRoot w := by
    change normalizedNegativeRoot (denominator A.matrix q) = normalizedNegativeRoot w
    rw [hDen]
    exact normalizedNegativeRoot_scale (by positivity) hw
  have hGeomNZ : (starRingEnd ℂ) (negativeSquareRootPhase A.matrix q) ≠ 0 := by
    apply (map_ne_zero (starRingEnd ℂ)).2
    rw [hGeom]
    have hS : Complex.sqrt w ≠ 0 := by rw [sqrt_eq_exp hw]; exact Complex.exp_ne_zero _
    have hN : 0 < ‖w‖ := norm_pos_iff.mpr hw
    exact mul_ne_zero (div_ne_zero hS
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hN).ne'))
      (div_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne') hw)
  have hCoeff : actualCrossPhase z ⟨D, A, 0⟩ *
      exponentialPhase (scaledCrossDiagonal (D + 1) (A.matrix 0 0) (A.matrix 1 1) : ℂ) =
      crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
        (starRingEnd ℂ) (negativeSquareRootPhase A.matrix q) := by
    rw [← analyticCrossEntry_eq hD A q, actualCrossPhase_zero, analyticCrossEntry, map_div₀]
    unfold exponentialPhase periodCoefficient
    change (starRingEnd ℂ) (oddEtaPhase (crossGroupElement A) (ModularGroup.S • q)) *
        (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S q) * _ = _
    field_simp [hGeomNZ] <;> ring
  have hAct : ((g • z : ℍ) : ℂ) = matrixMoebius g z := by
    simpa [matrixMoebius] using UpperHalfPlane.coe_specialLinearGroup_apply g z
  have hHt : (g • z).im = z.im / (c ^ 2 * (u ^ 2 + z.im ^ 2)) := by
    have hh := scaledCross_translate_height hD A z 0
    rw [translatePoint_zero, Int.cast_zero, zero_add] at hh
    exact hh
  have hExp : exponentialPhase ((oddInfinityFrequency : ℂ) * ((g • z : ℍ) : ℂ)) *
      exponentialPhase (((-oddZeroFrequency * z.re) : ℝ) : ℂ) =
      exponentialPhase (scaledCrossDiagonal (D + 1) (A.matrix 0 0) (A.matrix 1 1) : ℂ) *
        exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * w) -
          (oddZeroFrequency : ℂ) * (u : ℂ)) := by
    have hh := scaledCross_row_exponential_phase hD A (x := z.re) (y := z.im) z.im_pos
    dsimp only at hh
    rw [hPoint] at hh
    have hA : (scaledCrossMatrix A 1 0 : ℂ) = (c : ℂ) := by rw [scaledCrossMatrix_lowerLeft]
    rw [hA] at hh
    calc
      _ = exponentialPhase ((oddInfinityFrequency : ℂ) * matrixMoebius g z -
          (oddZeroFrequency : ℂ) * (z.re : ℂ)) := by
        rw [hAct]
        unfold exponentialPhase
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      _ = _ := hh
  unfold oddCrossFourierTerm oddCrossSeed
  simp only [translatePoint_zero]
  change actualCrossPhase z ⟨D, A, 0⟩ *
    (((g • z : ℍ).im : ℂ) ^ s * _) * _ = _
  calc
    _ = (actualCrossPhase z ⟨D, A, 0⟩ * (((g • z : ℍ).im : ℂ) ^ s)) *
        (exponentialPhase ((oddInfinityFrequency : ℂ) * ((g • z : ℍ) : ℂ)) *
          exponentialPhase (((-oddZeroFrequency * z.re) : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [hExp]
      unfold crossRealKernel
      change _ = crossEntry _ _ _ * ((starRingEnd ℂ) (normalizedNegativeRoot w) * _ * _)
      rw [← hGeom, ← hHt]
      calc
        _ = (actualCrossPhase z ⟨D, A, 0⟩ *
              exponentialPhase (scaledCrossDiagonal (D + 1) (A.matrix 0 0) (A.matrix 1 1) : ℂ)) *
            ((((g • z : ℍ).im : ℂ) ^ s) *
              exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * w) -
                (oddZeroFrequency : ℂ) * (u : ℂ))) := by ring
        _ = _ := by rw [hCoeff]; ring

end
end ManuscriptAudit.Paper8OddCrossPoincareRowKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareRowKernel.oddCrossFourierTerm_row_kernel
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
