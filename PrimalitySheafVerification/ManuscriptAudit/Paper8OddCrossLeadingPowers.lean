import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaFactorization

/-! Principal complex-power factorization of the leading cross-cusp Fourier kernel. -/

namespace ManuscriptAudit.Paper8OddCrossLeadingPowers

open Paper8OddCrossZetaFactorization Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareKernel
open Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareHeight MaassLaplacian
open Paper8OddCrossCuspNormalization

noncomputable section

private theorem log_norm_eq_average (w : ℂ) :
    (Real.log ‖w‖ : ℂ) = (Complex.log w + (starRingEnd ℂ) (Complex.log w)) / 2 := by
  apply Complex.ext
  · rw [Complex.ofReal_re, Complex.div_ofNat_re, Complex.add_re, Complex.conj_re, Complex.log_re]
    ring
  · rw [Complex.ofReal_im, Complex.div_ofNat_im, Complex.add_im, Complex.conj_im]
    ring

theorem conj_normalizedNegativeRoot_eq_exp {w : ℂ} (hw : w ≠ 0) :
    (starRingEnd ℂ) (normalizedNegativeRoot w) =
      Complex.exp ((Complex.log w - (starRingEnd ℂ) (Complex.log w)) / 4) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let r : ℂ := Real.log ‖w‖
  let l := Complex.log w
  have hR : Complex.exp r = (‖w‖ : ℂ) := by
    change Complex.exp ((Real.log ‖w‖ : ℝ) : ℂ) = _
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  have hS : (Real.sqrt ‖w‖ : ℂ) = Complex.exp (r / 2) := by
    change (Real.sqrt ‖w‖ : ℂ) = Complex.exp (((Real.log ‖w‖ : ℝ) : ℂ) / 2)
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hE₁ : Complex.sqrt w / (Real.sqrt ‖w‖ : ℂ) = Complex.exp (l / 2 - r / 2) := by
    rw [sqrt_eq_exp hw, hS, Complex.exp_sub]
  have hE₂ : (‖w‖ : ℂ) / w = Complex.exp (r - l) := by
    rw [Complex.exp_sub, hR, Complex.exp_log hw]
  have hN : normalizedNegativeRoot w = Complex.exp ((r - l) / 2) := by
    unfold normalizedNegativeRoot
    rw [hE₁, hE₂, ← Complex.exp_add]
    congr 1
    ring
  rw [hN, ← Complex.exp_conj]
  congr 1
  change (starRingEnd ℂ) ((r - l) / 2) = (l - (starRingEnd ℂ) l) / 4
  have hTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one]
  rw [map_div₀, map_sub, hTwo]
  have hr' : (starRingEnd ℂ) r = r := Complex.conj_ofReal _
  rw [hr', show r = (l + (starRingEnd ℂ) l) / 2 from log_norm_eq_average w]
  ring

theorem crossLeadingKernel_principal_powers (s : ℂ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    crossLeadingKernel s y u =
      (y : ℂ) ^ s * (complexPoint u y) ^ (1 / 4 - s) *
        ((starRingEnd ℂ) (complexPoint u y)) ^ (-(1 / 4 : ℂ) - s) *
        exponentialPhase (-(oddZeroFrequency : ℂ) * (u : ℂ)) := by
  let w := complexPoint u y
  let z := (starRingEnd ℂ) w
  let H := y / (u ^ 2 + y ^ 2)
  have hwI : w.im = y := complexPoint_im _ _
  have hw : w ≠ 0 := fun he => hy.ne' (by simpa only [hwI, Complex.zero_im] using congrArg Complex.im he)
  have hz : z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hw
  have hNormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwPi : w.arg ≠ Real.pi := fun h => hy.ne' (by rw [← hwI]; exact (Complex.arg_eq_pi_iff.mp h).2)
  have hNorm : ‖w‖ ^ 2 = u ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hwI]
    unfold w complexPoint
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  have hH : 0 < H := div_pos hy (by rw [← hNorm]; positivity)
  have hZ : Complex.log z = (starRingEnd ℂ) (Complex.log w) := Complex.log_conj w hwPi
  have hLog : Complex.log (H : ℂ) =
      Complex.log (y : ℂ) - Complex.log w - Complex.log z := by
    rw [← Complex.ofReal_log hH.le, ← Complex.ofReal_log hy.le]
    unfold H
    rw [← hNorm, Real.log_div hy.ne' (pow_ne_zero _ hNormPos.ne'), Real.log_pow, hZ]
    push_cast
    have hAvg := log_norm_eq_average w
    linear_combination -2 * hAvg
  change (starRingEnd ℂ) (normalizedNegativeRoot w) * (H : ℂ) ^ s *
      exponentialPhase (-(oddZeroFrequency : ℂ) * (u : ℂ)) =
    (y : ℂ) ^ s * w ^ (1 / 4 - s) * z ^ (-(1 / 4 : ℂ) - s) *
      exponentialPhase (-(oddZeroFrequency : ℂ) * (u : ℂ))
  rw [conj_normalizedNegativeRoot_eq_exp hw, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hH.ne') s,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') s, Complex.cpow_def_of_ne_zero hw,
    Complex.cpow_def_of_ne_zero hz, hLog]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  change Complex.exp ((Complex.log w - (starRingEnd ℂ) (Complex.log w)) / 4 +
      (Complex.log (y : ℂ) - Complex.log w - Complex.log z) * s) = _
  rw [hZ]
  congr 1
  ring

end
end ManuscriptAudit.Paper8OddCrossLeadingPowers

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossLeadingPowers.crossLeadingKernel_principal_powers
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
