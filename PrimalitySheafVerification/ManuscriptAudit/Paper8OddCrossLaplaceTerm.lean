import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.Indicator
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossAbelObstruction
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaFactorization

/-! Logarithmic support and exact half-line transforms of the individual signed coefficients. -/

namespace ManuscriptAudit.Paper8OddCrossLaplaceTerm

open Filter MeasureTheory Set
open Paper8OddCrossAbelObstruction Paper8OddCrossCuspCutoff Paper8OddCrossZetaFactorization
open scoped Nat

noncomputable section

def logarithmicThreshold (j : ℕ) : ℝ := Real.log ((j + 1 : ℕ) : ℝ)

def crossLaplaceTerm (w : ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  (Ici (logarithmicThreshold j)).indicator (fun t => crossRaw j * Complex.exp (-w * (t : ℂ))) t

theorem logarithmicThreshold_le_iff (j : ℕ) (t : ℝ) :
    logarithmicThreshold j ≤ t ↔ j < ⌊Real.exp t⌋₊ := by
  unfold logarithmicThreshold
  calc
    Real.log ((j + 1 : ℕ) : ℝ) ≤ t ↔ ((j + 1 : ℕ) : ℝ) ≤ Real.exp t := by
      conv_lhs => rw [← Real.log_exp t]
      exact Real.log_le_log_iff (by positivity) (Real.exp_pos t)
    _ ↔ j + 1 ≤ ⌊Real.exp t⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg t)).symm
    _ ↔ _ := Nat.succ_le_iff

private theorem logarithmicThreshold_nonneg (j : ℕ) : 0 ≤ logarithmicThreshold j := by
  unfold logarithmicThreshold
  exact Real.log_nonneg (by positivity)

private theorem setIntegral_logarithmic_indicator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E) (j : ℕ) :
    (∫ t in Ioi (0 : ℝ), (Ici (logarithmicThreshold j)).indicator g t) =
      ∫ t in Ioi (logarithmicThreshold j), g t := by
  have hI : Ici (0 : ℝ) ∩ Ici (logarithmicThreshold j) = Ici (logarithmicThreshold j) :=
    Set.inter_eq_right.mpr (Set.Ici_subset_Ici.mpr (logarithmicThreshold_nonneg j))
  calc
    _ = ∫ t in Ici (0 : ℝ), (Ici (logarithmicThreshold j)).indicator g t :=
      integral_Ici_eq_integral_Ioi.symm
    _ = ∫ t in Ici (logarithmicThreshold j), g t := by
      rw [setIntegral_indicator measurableSet_Ici, hI]
    _ = _ := integral_Ici_eq_integral_Ioi

theorem crossLaplaceTerm_integrable {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    IntegrableOn (crossLaplaceTerm w j) (Ioi 0) := by
  have hn : (-w).re < 0 := by simpa only [Complex.neg_re, neg_lt_zero] using hw
  exact ((integrableOn_exp_mul_complex_Ioi hn 0).const_mul (crossRaw j)).indicator measurableSet_Ici

theorem crossLaplaceTerm_integral {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    (∫ t in Ioi (0 : ℝ), crossLaplaceTerm w j t) =
      crossRaw j * ((((j + 1 : ℕ) : ℂ) ^ (-w)) / w) := by
  have hn : (-w).re < 0 := by simpa only [Complex.neg_re, neg_lt_zero] using hw
  have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hlog : ((logarithmicThreshold j : ℝ) : ℂ) = Complex.log ((j + 1 : ℕ) : ℂ) :=
    Complex.ofReal_log (by positivity : 0 ≤ ((j + 1 : ℕ) : ℝ))
  change (∫ t in Ioi (0 : ℝ), (Ici (logarithmicThreshold j)).indicator
    (fun u => crossRaw j * Complex.exp (-w * (u : ℂ))) t) = _
  rw [setIntegral_logarithmic_indicator, integral_const_mul,
    integral_exp_mul_complex_Ioi hn, hlog, Complex.cpow_def_of_ne_zero hk, mul_comm (-w)]
  simp [div_eq_mul_inv]

theorem crossLaplaceTerm_norm_integral {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖crossLaplaceTerm w j t‖) =
      (‖crossRaw j‖ / w.re) * (((j + 1 : ℕ) : ℝ) ^ (-w.re)) := by
  have hFn (t : ℝ) : ‖crossLaplaceTerm w j t‖ =
      (Ici (logarithmicThreshold j)).indicator
        (fun t => ‖crossRaw j‖ * Real.exp (-w.re * t)) t := by
    simp only [crossLaplaceTerm, norm_indicator_eq_indicator_norm, norm_mul,
      Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  simp_rw [hFn]
  rw [setIntegral_logarithmic_indicator, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hw),
    Real.rpow_def_of_pos (by positivity : 0 < ((j + 1 : ℕ) : ℝ))]
  unfold logarithmicThreshold
  rw [mul_comm (-w.re)]
  field_simp [hw.ne'] <;> ring

theorem norm_crossRaw_le_one (j : ℕ) : ‖crossRaw j‖ ≤ 1 := by
  have hPos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  unfold crossRaw
  rw [norm_div, Complex.norm_natCast, div_le_one hPos]
  exact norm_crossSum_le (Nat.succ_pos j)

end
end ManuscriptAudit.Paper8OddCrossLaplaceTerm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossLaplaceTerm.logarithmicThreshold_le_iff,
      ``ManuscriptAudit.Paper8OddCrossLaplaceTerm.crossLaplaceTerm_integral,
      ``ManuscriptAudit.Paper8OddCrossLaplaceTerm.crossLaplaceTerm_norm_integral] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
