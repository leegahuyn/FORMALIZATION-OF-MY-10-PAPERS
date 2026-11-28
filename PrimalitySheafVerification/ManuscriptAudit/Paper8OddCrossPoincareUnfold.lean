import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareRowKernel

/-! Absolute integrability of the cross-cusp kernel and exact Fourier unfolding of every normalized row. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareUnfold

open Set Filter MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspPhase
open Paper8OddCrossCuspCutoff Paper8OddCrossCuspActualMultiplier
open Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareHeight
open Paper8OddCrossPoincareKernel Paper8OddCrossScaledRows Paper8OddCrossPoincareTranslate
open Paper8OddCrossPoincareRowKernel

noncomputable section

private theorem pointAtHeight_ne_zero (u : ℝ) {y : ℝ} (hy : 0 < y) :
    complexPoint u y ≠ 0 := by
  intro h
  have hIm := congrArg Complex.im h
  change (complexPoint u y).im = 0 at hIm
  exact hy.ne' (by simpa only [complexPoint_im] using hIm)

private theorem kernelHeight_pos {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (u : ℝ) :
    0 < y / (c ^ 2 * (u ^ 2 + y ^ 2)) := by positivity

theorem crossRealKernel_continuous (s : ℂ) {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (crossRealKernel s y c) := by
  let w (u : ℝ) := complexPoint u y
  let h (u : ℝ) := y / (c ^ 2 * (u ^ 2 + y ^ 2))
  have hw (u : ℝ) : w u ≠ 0 := pointAtHeight_ne_zero u hy
  have hWC : Continuous w := by
    dsimp only [w, complexPoint]
    fun_prop
  have hHeight : Continuous h :=
    continuous_const.div (continuous_const.mul ((continuous_id.pow 2).add continuous_const))
      (fun _ => by positivity)
  have hS : Continuous (fun u => Complex.sqrt (w u)) := by
    have hLog : Continuous (fun u => Complex.log (w u)) :=
      hWC.clog (fun u => Or.inr (by simpa only [w, complexPoint_im] using hy.ne'))
    have he : Continuous (fun u => Complex.exp (Complex.log (w u) / 2)) :=
      Complex.continuous_exp.comp (hLog.div_const 2)
    have hEq : (fun u => Complex.sqrt (w u)) = (fun u => Complex.exp (Complex.log (w u) / 2)) :=
      funext fun u => sqrt_eq_exp (hw u)
    rwa [hEq]
  have hNorm : Continuous (fun u => (‖w u‖ : ℂ)) := Complex.continuous_ofReal.comp hWC.norm
  have hNormSqrt : Continuous (fun u => (Real.sqrt ‖w u‖ : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hWC.norm)
  have hRoot : Continuous (fun u => normalizedNegativeRoot (w u)) := by
    unfold normalizedNegativeRoot
    exact (hS.div hNormSqrt (fun u => Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (norm_pos_iff.mpr (hw u))).ne')).mul (hNorm.div hWC hw)
  have hPow : Continuous (fun u => (h u : ℂ) ^ s) :=
    (Complex.continuous_ofReal.comp hHeight).cpow continuous_const (fun u =>
      Or.inl (by
        change 0 < ((h u : ℝ) : ℂ).re
        rw [Complex.ofReal_re]
        exact kernelHeight_pos hy hc u))
  have hDen : Continuous (fun u => (c : ℂ) ^ 2 * w u) := continuous_const.mul hWC
  have hDen0 (u : ℝ) : (c : ℂ) ^ 2 * w u ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne')) (hw u)
  have hExp : Continuous (fun u : ℝ => exponentialPhase
      (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * w u) - (oddZeroFrequency : ℂ) * (u : ℂ))) := by
    apply Complex.continuous_exp.comp
    exact continuous_const.mul ((continuous_const.div hDen hDen0).sub
      (continuous_const.mul Complex.continuous_ofReal))
  exact ((Complex.continuous_conj.comp hRoot).mul hPow).mul hExp

private theorem kernelExponential_norm_le {y c : ℝ} (hy : 0 < y) (u : ℝ) :
    ‖exponentialPhase (-(oddInfinityFrequency : ℂ) / ((c : ℂ) ^ 2 * complexPoint u y) -
      (oddZeroFrequency : ℂ) * (u : ℂ))‖ ≤ 1 := by
  let v : ℂ := (c : ℂ) ^ 2 * complexPoint u y
  let b : ℂ := -(oddInfinityFrequency : ℂ) / v - (oddZeroFrequency : ℂ) * (u : ℂ)
  have hV : v.im = c ^ 2 * y := by
    change (((c : ℂ) ^ 2) * complexPoint u y).im = _
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, complexPoint_im, zero_mul, add_zero]
  have hI : b.im = oddInfinityFrequency * v.im / Complex.normSq v := by
    dsimp only [b]
    simp [Complex.sub_im, Complex.div_im, Complex.mul_im] <;> ring
  have hNN : 0 ≤ b.im := by
    rw [hI, hV]
    exact div_nonneg (mul_nonneg (by norm_num [oddInfinityFrequency])
      (mul_nonneg (sq_nonneg _) hy.le)) (Complex.normSq_nonneg v)
  change ‖exponentialPhase b‖ ≤ 1
  rw [exponentialPhase, Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hR : (2 * (Real.pi : ℂ) * Complex.I * b).re = -(2 * Real.pi * b.im) := by
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hR]
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hNN)

theorem crossRealKernel_integrable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable (crossRealKernel s y c) := by
  let a : ℝ := min (y ^ 2) 1
  let C : ℝ := y / (c ^ 2 * a)
  have ha : 0 < a := lt_min (sq_pos_of_pos hy) zero_lt_one
  have hC : 0 < C := by dsimp only [C]; positivity
  have hRank : (Module.finrank ℝ ℝ : ℝ) < 2 * s.re := by
    rw [Module.finrank_self, Nat.cast_one]
    linarith
  have hM : Integrable (fun u : ℝ => ((1 : ℝ) + u ^ 2) ^ (-s.re)) := by
    have hJ := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hRank
    simpa only [Real.norm_eq_abs, sq_abs, show (-(2 * s.re) / 2 : ℝ) = -s.re by ring] using hJ
  refine (hM.const_mul (C ^ s.re)).mono' (crossRealKernel_continuous s hy hc).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun u => ?_)
  have hN := normalizedNegativeRoot_norm (pointAtHeight_ne_zero u hy)
  have hE := kernelExponential_norm_le (c := c) hy u
  have hQ : a * (1 + u ^ 2) ≤ u ^ 2 + y ^ 2 := by
    have h1 : a ≤ 1 := min_le_right _ _
    have h2 : a ≤ y ^ 2 := min_le_left _ _
    rw [mul_add, mul_one]
    linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg u)]
  have hHt : y / (c ^ 2 * (u ^ 2 + y ^ 2)) ≤ C / (1 + u ^ 2) := by
    have hcQ : 0 < c ^ 2 * (u ^ 2 + y ^ 2) := by positivity
    rw [show C = y / (c ^ 2 * a) from rfl, div_div]
    exact div_le_div_of_nonneg_left hy.le (by positivity)
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hQ (sq_nonneg c))
  unfold crossRealKernel
  rw [norm_mul, norm_mul, Complex.norm_conj, hN, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (kernelHeight_pos hy hc u)]
  calc
    _ ≤ (y / (c ^ 2 * (u ^ 2 + y ^ 2))) ^ s.re :=
      mul_le_of_le_one_right (Real.rpow_nonneg (kernelHeight_pos hy hc u).le _) hE
    _ ≤ (C / (1 + u ^ 2)) ^ s.re :=
      Real.rpow_le_rpow (kernelHeight_pos hy hc u).le hHt (by linarith)
    _ = _ := by
      rw [Real.div_rpow hC.le (by positivity), div_eq_mul_inv, Real.rpow_neg (by positivity)]

def pointAtHeight (x : ℝ) {y : ℝ} (hy : 0 < y) : ℍ :=
  ⟨complexPoint x y, by rwa [complexPoint_im]⟩

theorem pointAtHeight_re (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (pointAtHeight x hy).re = x := by
  change (complexPoint x y).re = x
  simp [complexPoint, Complex.add_re, Complex.mul_re]

theorem pointAtHeight_im (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (pointAtHeight x hy).im = y := by
  change (complexPoint x y).im = y
  exact complexPoint_im x y

theorem translatePoint_pointAtHeight_im (n : ℤ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (translatePoint n (pointAtHeight x hy)).im = y := by
  change ((translatePoint n (pointAtHeight x hy) : ℍ) : ℂ).im = y
  rw [translatePoint_coe, Complex.add_im, Complex.intCast_im, zero_add]
  exact pointAtHeight_im x hy

theorem hasSum_oddCross_row_fourier {D : ℕ} (A : CrossRow (D + 1)) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..(1 : ℝ), oddCrossFourierTerm s (pointAtHeight x hy) ⟨D, A, n⟩)
      (crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
        ∫ u : ℝ, crossRealKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u) := by
  let c : ℝ := 2 * ((D + 1 : ℕ) : ℝ)
  let b := crossRowShift A
  let K (u : ℝ) := crossRealKernel s y c u
  let a := crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1)
  have hK : Integrable K := crossRealKernel_integrable s hs hy (by dsimp only [c]; positivity)
  have hS := (hK.hasSum_intervalIntegral b).mul_left a
  refine hS.congr_fun (fun n => ?_)
  rw [← intervalIntegral.integral_const_mul]
  have hTrans : (∫ x in (0 : ℝ)..(1 : ℝ), a * K (x + (b + (n : ℝ)))) =
      ∫ u in b + (n : ℝ)..b + (n : ℝ) + 1, a * K u := by
    simpa only [zero_add, add_comm (1 : ℝ)] using
      intervalIntegral.integral_comp_add_right (a := 0) (b := 1) (f := fun u => a * K u) (b + (n : ℝ))
  rw [← hTrans]
  apply intervalIntegral.integral_congr
  intro x _
  change oddCrossFourierTerm s (pointAtHeight x hy) ⟨D, A, n⟩ = a * K (x + (b + (n : ℝ)))
  rw [oddCrossFourierTerm_translate A n s (pointAtHeight x hy), oddCrossFourierTerm_row_kernel,
    translatePoint_re, pointAtHeight_re]
  rw [translatePoint_pointAtHeight_im]
  unfold K b c a
  rw [show x + (crossRowShift A + (n : ℝ)) = (n : ℝ) + x + crossRowShift A by ring]

theorem hasSum_oddCross_modulus_fourier {D : ℕ} (hOdd : Odd (D + 1)) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) {y : ℝ} (hy : 0 < y) :
    letI := analyticCrossFintype (Nat.succ_pos D) hOdd
    HasSum (fun n : ℤ => ∑ A : CrossRow (D + 1), ∫ x in (0 : ℝ)..(1 : ℝ),
      oddCrossFourierTerm s (pointAtHeight x hy) ⟨D, A, n⟩)
      (crossSum (Nat.succ_pos D) * ∫ u : ℝ, crossRealKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u) := by
  letI := analyticCrossFintype (Nat.succ_pos D) hOdd
  let C (A : CrossRow (D + 1)) := crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1)
  let K := ∫ u : ℝ, crossRealKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u
  have hSum : crossSum (Nat.succ_pos D) = ∑ A : CrossRow (D + 1), C A := by
    rw [crossSum_eq_analytic (Nat.succ_pos D) hOdd (pointAtHeight 0 hy)]
    exact Finset.sum_congr rfl (fun A _ => analyticCrossEntry_eq (Nat.succ_pos D) A _)
  have hRows : HasSum (fun n : ℤ => ∑ A : CrossRow (D + 1), ∫ x in (0 : ℝ)..(1 : ℝ),
      oddCrossFourierTerm s (pointAtHeight x hy) ⟨D, A, n⟩)
      (∑ A : CrossRow (D + 1), C A * K) := by
    apply hasSum_sum
    intro A _
    exact hasSum_oddCross_row_fourier A s hs hy
  rw [← Finset.sum_mul, ← hSum] at hRows
  exact hRows

end
end ManuscriptAudit.Paper8OddCrossPoincareUnfold

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareUnfold.hasSum_oddCross_modulus_fourier
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
