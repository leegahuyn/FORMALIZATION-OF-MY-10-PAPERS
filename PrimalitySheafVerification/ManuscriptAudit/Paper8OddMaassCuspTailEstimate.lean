import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8HighStripFubini
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassHorizontalPoincare

/-! A uniform inverse-square cusp-tail bound for the actual odd Maass chart family. -/

namespace ManuscriptAudit.Paper8OddMaassCuspTailEstimate

open MeasureTheory Set UpperHalfPlane
open Paper8HighStripFubini Paper8OddMaassHorizontalPoincare Paper8OddAllCuspMonodromy
open Paper8OddMaassHilbertCore Paper8OddCosetChartTransition Paper8OddCosetChartEnergy
open Paper8OddCosetChartDifferential Paper8MaassCovariantPullback
open FiniteIndexWeightZeroCosets
open scoped ENNReal MatrixGroups

noncomputable section

theorem continuous_oddCosetChartMassAt (f : OddSmoothCompactCore) :
    Continuous (oddCosetChartMassAt (f : ℂ → ℂ)) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  unfold oddCosetChartMassAt
  apply continuous_finsetSum
  intro q _
  simpa only [oddCosetPullback_coe] using (oddCosetPullback_continuous f q).norm.pow 2

theorem oddCosetChartMassAt_nonneg (F : ℂ → ℂ) (z : ℍ) : 0 ≤ oddCosetChartMassAt F z := by
  unfold oddCosetChartMassAt
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem oddCosetChartTotalEnergy_nonneg (f : OddSmoothCompactCore) (z : ℍ) :
    0 ≤ oddCosetChartTotalEnergy f z := by
  unfold oddCosetChartTotalEnergy oddCosetChartEnergyAt maassCovariantEnergy
  exact add_nonneg (Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (oddCosetChartMassAt_nonneg _ _)

def standardCuspTail (T : ℝ) : Set ℍ := ModularGroup.fd ∩ {z : ℍ | T ≤ z.im}

theorem standardCuspTail_eq_highStrip {T : ℝ} (hT : 1 ≤ T) :
    standardCuspTail T = highHorizontalStrip (-(1 / 2)) (1 / 2) T := by
  ext z
  constructor
  · intro hz
    exact ⟨abs_le.mp hz.1.2, hz.2⟩
  · intro hz
    have hy : 1 ≤ z.im := hT.trans hz.2
    have hSq := pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hy 2
    have hN : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two, pow_two]
    have hC : 1 ≤ Complex.normSq (z : ℂ) := by
      rw [hN]
      nlinarith only [hSq, sq_nonneg z.re]
    exact ⟨⟨hC, abs_le.mpr hz.1⟩, hz.2⟩

def oddCuspTailConstant : ℝ := 32 / ‖periodFourPhase - 1‖ ^ 2

theorem oddCuspTailConstant_nonneg : 0 ≤ oddCuspTailConstant := by
  unfold oddCuspTailConstant
  positivity

theorem oddCosetChart_lintegral_cusp_tail_le (f : OddSmoothCompactCore) {T : ℝ} (hT : 1 ≤ T) :
    (∫⁻ z in standardCuspTail T, ENNReal.ofReal (oddCosetChartMassAt (f : ℂ → ℂ) z)) ≤
      ENNReal.ofReal (oddCuspTailConstant / T ^ 2) *
        ∫⁻ z in ModularGroup.fd, ENNReal.ofReal (oddCosetChartTotalEnergy f z) := by
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  let M := oddCosetChartMassAt (f : ℂ → ℂ)
  let E := oddCosetChartTotalEnergy f
  let C := oddCuspTailConstant / T ^ 2
  have hab : a ≤ b := by norm_num [a, b]
  have hB : a + 1 = b := by norm_num [a, b]
  have hM : Continuous M := continuous_oddCosetChartMassAt f
  have hE : Continuous E := continuous_oddCosetChartTotalEnergy f
  have hE₀ : ∀ z, 0 ≤ E z := oddCosetChartTotalEnergy_nonneg f
  have hC : 0 ≤ C := div_nonneg oddCuspTailConstant_nonneg (sq_nonneg _)
  have hPoint (y : ℝ) (hy : y ∈ Ici T) :
      weightedHorizontalSlice M a b y ≤ weightedHorizontalSlice (fun z => C * E z) a b y := by
    have hy' : 1 ≤ y := hT.trans hy
    have hp : 0 < y := zero_lt_one.trans_le hy'
    have hU (x : ℝ) : upperStripPoint x y = horizontalUpperPoint x hp := by
      apply UpperHalfPlane.ext
      change MaassLaplacian.complexPoint x (max y 1) = MaassLaplacian.complexPoint x y
      rw [max_eq_left hy']
    have hHor := oddCosetChart_horizontal_mass_le f hp a
    rw [hB] at hHor
    simp only [← hU] at hHor
    change (∫ x in a..b, M (upperStripPoint x y)) ≤
      (oddCuspTailConstant / y ^ 2) * ∫ x in a..b, E (upperStripPoint x y) at hHor
    have hI : 0 ≤ ∫ x in a..b, E (upperStripPoint x y) :=
      intervalIntegral.integral_nonneg hab (fun x _ => hE₀ _)
    have hD : oddCuspTailConstant / y ^ 2 ≤ C :=
      div_le_div_of_nonneg_left oddCuspTailConstant_nonneg
        (sq_pos_of_pos (zero_lt_one.trans_le hT))
        (pow_le_pow_left₀ (zero_lt_one.trans_le hT).le hy 2)
    unfold weightedHorizontalSlice
    rw [intervalIntegral.integral_const_mul]
    exact div_le_div_of_nonneg_right
      (hHor.trans (mul_le_mul_of_nonneg_right hD hI)) (sq_nonneg y)
  have hTail :
      (∫⁻ z in standardCuspTail T, ENNReal.ofReal (M z)) ≤
        ∫⁻ z in standardCuspTail T, ENNReal.ofReal (C * E z) := by
    rw [standardCuspTail_eq_highStrip hT]
    change (∫⁻ z in highHorizontalStrip a b T, ENNReal.ofReal (M z)) ≤
      ∫⁻ z in highHorizontalStrip a b T, ENNReal.ofReal (C * E z)
    rw [lintegral_hyperbolic_highStrip hM (oddCosetChartMassAt_nonneg _) hab hT,
      lintegral_hyperbolic_highStrip (continuous_const.mul hE) (fun z => mul_nonneg hC (hE₀ z)) hab hT]
    exact setLIntegral_mono' measurableSet_Ici (fun y hy => ENNReal.ofReal_le_ofReal (hPoint y hy))
  calc
    _ ≤ ∫⁻ z in standardCuspTail T, ENNReal.ofReal (C * E z) := hTail
    _ ≤ ∫⁻ z in ModularGroup.fd, ENNReal.ofReal (C * E z) :=
      lintegral_mono_set inter_subset_left
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hE.measurable)

end
end ManuscriptAudit.Paper8OddMaassCuspTailEstimate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCuspTailEstimate.oddCosetChart_lintegral_cusp_tail_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
