import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaFactorization
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareUnfold

/-! The explicit arithmetic zeta remainder converges absolutely to the right of Re(s) = 1/2. -/

namespace ManuscriptAudit.Paper8OddCrossZetaRemainder

open Filter MeasureTheory MaassLaplacian Paper8OddCrossScaledRows
open Paper8OddCrossPoincareKernel Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareUnfold
open Paper8OddCrossZetaFactorization

noncomputable section

def crossCorrection (y c u : ℝ) : ℂ :=
  exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * complexPoint u y))

private def dampingConstant : ℝ := 2 * Real.pi * oddInfinityFrequency

private theorem dampingConstant_pos : 0 < dampingConstant := by
  unfold dampingConstant oddInfinityFrequency
  positivity

private theorem point_norm_ge {y : ℝ} (hy : 0 < y) (u : ℝ) : y ≤ ‖complexPoint u y‖ := by
  have h := Complex.abs_im_le_norm (complexPoint u y)
  rw [complexPoint_im, abs_of_pos hy] at h
  exact h

private def correctionExponent (y c u : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I *
    (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * complexPoint u y))

private theorem correctionExponent_norm_le {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (u : ℝ) :
    ‖correctionExponent y c u‖ ≤ dampingConstant / (c ^ 2 * y) := by
  have hμ : 0 < oddInfinityFrequency := by norm_num [oddInfinityFrequency]
  have hNorm : ‖correctionExponent y c u‖ =
      dampingConstant / (c ^ 2 * ‖complexPoint u y‖) := by
    unfold correctionExponent dampingConstant
    simp [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hμ, abs_of_pos hc] <;> ring
  rw [hNorm]
  exact div_le_div_of_nonneg_left dampingConstant_pos.le (by positivity)
    (mul_le_mul_of_nonneg_left (point_norm_ge hy u) (sq_nonneg c))

private theorem crossCorrection_continuous {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (crossCorrection y c) := by
  have hP : Continuous (fun u : ℝ => complexPoint u y) := by unfold complexPoint; fun_prop
  have hN (u : ℝ) : ((c : ℂ) ^ 2 * complexPoint u y) ≠ 0 := by
    have hW : 0 < ‖complexPoint u y‖ := hy.trans_le (point_norm_ge hy u)
    exact mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hc.ne')) (norm_pos_iff.mp hW)
  apply Complex.continuous_exp.comp
  exact continuous_const.mul (continuous_const.div (continuous_const.mul hP) hN)

private theorem crossCorrection_ne_zero (y c u : ℝ) : crossCorrection y c u ≠ 0 :=
  Complex.exp_ne_zero _

private theorem crossLeadingKernel_quotient (s : ℂ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    crossLeadingKernel s y u = crossRealKernel s y 1 u / crossCorrection y 1 u := by
  rw [crossRealKernel_factor s hy zero_lt_one, crossModulusFactor, one_pow, inv_one, Complex.ofReal_one,
    Complex.one_cpow, one_mul]
  have hEq : crossRemainderKernel s y 1 u = crossLeadingKernel s y u * (crossCorrection y 1 u - 1) := rfl
  rw [hEq]
  apply (eq_div_iff (crossCorrection_ne_zero y 1 u)).2
  ring

theorem crossLeadingKernel_continuous (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (crossLeadingKernel s y) := by
  have hF : crossLeadingKernel s y = (fun u => crossRealKernel s y 1 u / crossCorrection y 1 u) :=
    funext (crossLeadingKernel_quotient s hy)
  rw [hF]
  exact (crossRealKernel_continuous s hy zero_lt_one).div
    (crossCorrection_continuous hy zero_lt_one) (crossCorrection_ne_zero y 1)

private theorem lower_crossCorrection {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Real.exp (-(dampingConstant / y)) ≤ ‖crossCorrection y 1 u‖ := by
  have h := correctionExponent_norm_le hy zero_lt_one u
  simp only [one_pow, one_mul] at h
  change _ ≤ ‖Complex.exp (correctionExponent y 1 u)‖
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((neg_le_neg h).trans
    (abs_le.mp (Complex.abs_re_le_norm (correctionExponent y 1 u))).1)

theorem crossLeadingKernel_integrable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) {y : ℝ} (hy : 0 < y) :
    Integrable (crossLeadingKernel s y) := by
  refine ((crossRealKernel_integrable s hs hy zero_lt_one).norm.const_mul
    (Real.exp (dampingConstant / y))).mono' (crossLeadingKernel_continuous s hy).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun u => ?_)
  rw [crossLeadingKernel_quotient s hy, norm_div]
  calc
    _ ≤ ‖crossRealKernel s y 1 u‖ / Real.exp (-(dampingConstant / y)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (Real.exp_pos _) (lower_crossCorrection hy u)
    _ = _ := by rw [Real.exp_neg, div_inv_eq_mul, mul_comm]

def crossRemainderConstant (y : ℝ) : ℝ :=
  (dampingConstant / y) * Real.exp (dampingConstant / y)

theorem crossRemainderConstant_nonneg {y : ℝ} (hy : 0 < y) :
    0 ≤ crossRemainderConstant y := by
  unfold crossRemainderConstant
  exact mul_nonneg (div_nonneg dampingConstant_pos.le hy.le) (Real.exp_pos _).le

theorem crossRemainderKernel_norm_le (s : ℂ) {y c : ℝ} (hy : 0 < y) (hc : 1 ≤ c) (u : ℝ) :
    ‖crossRemainderKernel s y c u‖ ≤ (crossRemainderConstant y / c ^ 2) * ‖crossLeadingKernel s y u‖ := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hE := correctionExponent_norm_le hy hc0 u
  have hc2 : 1 ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1)]
  have hValue : ‖correctionExponent y c u‖ ≤ dampingConstant / y :=
    hE.trans (div_le_div_of_nonneg_left dampingConstant_pos.le hy (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 hy.le))
  have hDiff : ‖crossCorrection y c u - 1‖ ≤
      ‖correctionExponent y c u‖ * Real.exp ‖correctionExponent y c u‖ := by
    change ‖Complex.exp (correctionExponent y c u) - 1‖ ≤ _
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (correctionExponent y c u) 1
  have hBound := hDiff.trans (mul_le_mul hE (Real.exp_le_exp.mpr hValue)
    (Real.exp_pos _).le (div_nonneg dampingConstant_pos.le (by positivity)))
  change ‖crossLeadingKernel s y u * (crossCorrection y c u - 1)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖crossLeadingKernel s y u‖ * ((dampingConstant / (c ^ 2 * y)) *
        Real.exp (dampingConstant / y)) := mul_le_mul_of_nonneg_left hBound (norm_nonneg _)
    _ = _ := by
      unfold crossRemainderConstant
      field_simp [hc0.ne', hy.ne'] <;> ring

theorem crossRemainderKernel_integrable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) {y c : ℝ}
    (hy : 0 < y) (hc : 1 ≤ c) : Integrable (crossRemainderKernel s y c) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hC : Continuous (crossRemainderKernel s y c) :=
    (crossLeadingKernel_continuous s hy).mul ((crossCorrection_continuous hy hc0).sub continuous_const)
  refine ((crossLeadingKernel_integrable s hs hy).norm.const_mul
    (crossRemainderConstant y / c ^ 2)).mono' hC.aestronglyMeasurable ?_
  exact Eventually.of_forall (crossRemainderKernel_norm_le s hy hc)

theorem norm_integral_crossRemainderKernel_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) {y c : ℝ}
    (hy : 0 < y) (hc : 1 ≤ c) :
    ‖∫ u : ℝ, crossRemainderKernel s y c u‖ ≤
      (crossRemainderConstant y / c ^ 2) * ∫ u : ℝ, ‖crossLeadingKernel s y u‖ := by
  have hK := crossRemainderKernel_integrable s hs hy hc
  have hL := (crossLeadingKernel_integrable s hs hy).norm.const_mul (crossRemainderConstant y / c ^ 2)
  calc
    _ ≤ ∫ u : ℝ, ‖crossRemainderKernel s y c u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, (crossRemainderConstant y / c ^ 2) * ‖crossLeadingKernel s y u‖ :=
      integral_mono hK.norm hL (crossRemainderKernel_norm_le s hy hc)
    _ = _ := integral_const_mul _ _

def oddCrossRemainderTerm (s : ℂ) (y : ℝ) (D : ℕ) : ℂ :=
  oddCrossZetaTerm s D * ∫ u : ℝ, crossRemainderKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u

theorem oddCrossRemainderTerm_abs_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) {y : ℝ} (hy : 0 < y) :
    Summable (fun D : ℕ => ‖oddCrossRemainderTerm s y D‖) := by
  let L := ∫ u : ℝ, ‖crossLeadingKernel s y u‖
  let C := (2 : ℝ) ^ (-2 * s.re) * (crossRemainderConstant y / 4) * L
  have hL : 0 ≤ L := integral_nonneg (fun _ => norm_nonneg _)
  have hR := crossRemainderConstant_nonneg hy
  have hS : Summable (fun D : ℕ => ((D : ℝ) + 1) ^ (-1 - 2 * s.re)) :=
    ((Real.summable_one_div_nat_add_rpow 1 (1 + 2 * s.re)).2 (by linarith)).congr (fun D => by
      rw [abs_of_nonneg (by positivity : 0 ≤ (D : ℝ) + 1), one_div,
        ← Real.rpow_neg (by positivity : 0 ≤ (D : ℝ) + 1)]
      congr 1
      ring)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hS.mul_left C)
  intro D
  let N : ℝ := (D : ℝ) + 1
  have hN : 0 < N := by dsimp only [N]; positivity
  have hc : 1 ≤ 2 * ((D + 1 : ℕ) : ℝ) := by
    push_cast
    have hn : 0 ≤ (D : ℝ) := by positivity
    linarith
  have hB := norm_integral_crossRemainderKernel_le s hs hy hc
  have hTerm := mul_le_mul (norm_oddCrossZetaTerm_le s D) hB (norm_nonneg _)
    (by positivity : 0 ≤ (2 : ℝ) ^ (-2 * s.re) * ((D : ℝ) + 1) ^ (1 - 2 * s.re))
  rw [oddCrossRemainderTerm, norm_mul]
  refine hTerm.trans_eq ?_
  push_cast
  change (2 : ℝ) ^ (-2 * s.re) * N ^ (1 - 2 * s.re) *
    (crossRemainderConstant y / (2 * N) ^ 2 * L) = C * N ^ (-1 - 2 * s.re)
  have hPow : N ^ (-1 - 2 * s.re) = N ^ (1 - 2 * s.re) * (N ^ 2)⁻¹ := by
    rw [show (-1 - 2 * s.re : ℝ) = (1 - 2 * s.re) + (-2) by ring, Real.rpow_add hN,
      Real.rpow_neg hN.le, show N ^ (2 : ℝ) = N ^ (2 : ℕ) from Real.rpow_natCast N 2]
  rw [hPow]
  unfold C
  field_simp [hN.ne'] <;> ring

end
end ManuscriptAudit.Paper8OddCrossZetaRemainder

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossZetaRemainder.oddCrossRemainderTerm_abs_summable
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
