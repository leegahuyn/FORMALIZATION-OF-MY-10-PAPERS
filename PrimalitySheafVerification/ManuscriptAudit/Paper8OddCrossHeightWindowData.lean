import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLeadingPowers
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLocalizedRows

/-! Joint continuity and geometric support of the actual phase in log-height coordinates. -/

namespace ManuscriptAudit.Paper8OddCrossHeightWindowData

open Paper8OddCrossLeadingPowers Paper8OddCrossLocalizedKernel Paper8OddCrossLocalizedRows
open Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareKernel Paper8OddCrossCuspNormalization
open MaassLaplacian Set
open scoped Topology

noncomputable section

theorem continuous_cross_phase_logHeight {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : ℝ × ℝ => crossRealKernel 0 (Real.exp p.1) c p.2) := by
  let W (p : ℝ × ℝ) : ℂ := complexPoint p.2 (Real.exp p.1)
  have hWC : Continuous W := by
    unfold W complexPoint
    fun_prop
  have hWI (p : ℝ × ℝ) : 0 < (W p).im := by
    change 0 < (complexPoint p.2 (Real.exp p.1)).im
    rw [complexPoint_im]
    exact Real.exp_pos _
  have hW (p : ℝ × ℝ) : W p ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    rw [Complex.zero_im] at hi
    exact (hWI p).ne' hi
  have hL : Continuous (fun p => Complex.log (W p)) := hWC.clog fun p => Or.inr (hWI p).ne'
  have hR : Continuous (fun p => Complex.exp
      ((Complex.log (W p) - (starRingEnd ℂ) (Complex.log (W p))) / 4)) :=
    Complex.continuous_exp.comp ((hL.sub (Complex.continuous_conj.comp hL)).div_const 4)
  have hDen : Continuous (fun p => (c : ℂ) ^ 2 * W p) := continuous_const.mul hWC
  have hDen0 (p : ℝ × ℝ) : (c : ℂ) ^ 2 * W p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne')) (hW p)
  have hHoriz : Continuous (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hE : Continuous (fun p : ℝ × ℝ => exponentialPhase
      (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * W p) - (oddZeroFrequency : ℂ) * (p.2 : ℂ))) := by
    apply Complex.continuous_exp.comp
    exact continuous_const.mul ((continuous_const.div hDen hDen0).sub (continuous_const.mul hHoriz))
  have hEq (p : ℝ × ℝ) :
      crossRealKernel 0 (Real.exp p.1) c p.2 =
        Complex.exp ((Complex.log (W p) - (starRingEnd ℂ) (Complex.log (W p))) / 4) *
        exponentialPhase
          (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * W p) - (oddZeroFrequency : ℂ) * (p.2 : ℂ)) := by
    unfold crossRealKernel
    dsimp only
    rw [Complex.cpow_zero, mul_one]
    rw [← conj_normalizedNegativeRoot_eq_exp (hW p)] <;> rfl
  simp_rw [hEq]
  exact hR.mul hE

theorem crossInvertedHeight_large_modulus_le {y : ℝ} (hy : 0 < y)
    {D : ℕ} (hD : 2 ≤ D) (u : ℝ) :
    crossInvertedHeight y (2 * (D : ℝ)) u ≤ 1 / (16 * y) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hC : (16 : ℝ) ≤ (2 * (D : ℝ)) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) hD' 2
    nlinarith
  have hU : y ^ 2 ≤ u ^ 2 + y ^ 2 := le_add_of_nonneg_left (sq_nonneg u)
  have hDeno := mul_le_mul hC hU (sq_nonneg y) (sq_nonneg (2 * (D : ℝ)))
  unfold crossInvertedHeight
  calc
    _ ≤ y / (16 * y ^ 2) := div_le_div_of_nonneg_left hy.le (by positivity) hDeno
    _ = _ := by field_simp [hy.ne'] <;> ring

theorem crossInvertedHeight_two_cutoff_iff {q y : ℝ} (hq : 0 < q) (hy : 0 < y) (u : ℝ) :
    q < crossInvertedHeight y 2 u ↔ u ^ 2 < y / (4 * q) - y ^ 2 := by
  unfold crossInvertedHeight
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, lt_div_iff₀ (by positivity), lt_sub_iff_add_lt,
    lt_div_iff₀ (by positivity)]
  rw [show q * (4 * (u ^ 2 + y ^ 2)) = (u ^ 2 + y ^ 2) * (4 * q) by ring]

theorem crossInvertedHeight_two_cutoff_interval {q y : ℝ} (hq : 0 < q) (hy : 0 < y)
    (hRadius : 0 < y / (4 * q) - y ^ 2) (u : ℝ) :
    q < crossInvertedHeight y 2 u ↔
      u ∈ Ioo (-Real.sqrt (y / (4 * q) - y ^ 2)) (Real.sqrt (y / (4 * q) - y ^ 2)) := by
  rw [crossInvertedHeight_two_cutoff_iff hq hy u, ← Real.sq_sqrt hRadius.le, sq_lt_sq,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_lt] <;> rfl

end
end ManuscriptAudit.Paper8OddCrossHeightWindowData

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossHeightWindowData.continuous_cross_phase_logHeight,
      ``ManuscriptAudit.Paper8OddCrossHeightWindowData.crossInvertedHeight_large_modulus_le,
      ``ManuscriptAudit.Paper8OddCrossHeightWindowData.crossInvertedHeight_two_cutoff_interval] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
