import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FloquetFamilyPoincare
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCosetChartDifferential

/-! The actual odd Maass charts satisfy a horizontal covariant mass estimate with a height-squared gain. -/

namespace ManuscriptAudit.Paper8OddMaassHorizontalPoincare

open MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8OddAllCuspMonodromy Paper8OddCuspFloquetPhase Paper8FloquetFamilyPoincare
open Paper8OddMaassHilbertCore Paper8OddCosetChartTransition Paper8OddCosetChartEnergy
open Paper8OddCosetChartDifferential Paper8EtaCosetMass FiniteIndexWeightZeroCosets
open Paper8MaassCovariantGeometry Paper8MaassCovariantPullback
open scoped MatrixGroups

noncomputable section

def horizontalUpperPoint (x : ℝ) {y : ℝ} (hy : 0 < y) : ℍ :=
  ⟨complexPoint x y, by simpa only [complexPoint_im] using hy⟩

theorem horizontalUpperPoint_im (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (horizontalUpperPoint x hy).im = y := by
  change (complexPoint x y).im = y
  exact complexPoint_im x y

theorem continuous_horizontalUpperPoint {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => horizontalUpperPoint x hy) :=
  (show Continuous (fun x : ℝ => complexPoint x y) from
    Complex.continuous_ofReal.add continuous_const).upperHalfPlaneMk
      (fun x => by simpa only [complexPoint_im] using hy)

private theorem T_horizontalUpperPoint (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ModularGroup.T • horizontalUpperPoint x hy = horizontalUpperPoint (x + 1) hy := by
  rw [UpperHalfPlane.modular_T_smul]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd]
  change (((1 : ℝ) : ℂ) + complexPoint x y) = complexPoint (x + 1) y
  unfold complexPoint
  push_cast
  ring

theorem oddCosetPullback_hasDerivAt (f : OddSmoothCompactCore) (q : levelFourRightCoset)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => oddCosetPullback f q (horizontalUpperPoint t hy))
      (fderiv ℝ (oddCosetPullback f q) (horizontalUpperPoint x hy : ℂ) 1) x := by
  have h := oddCosetPullback_differentiableAt f q (horizontalUpperPoint x hy)
  have hX : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x := by
    simpa only [id_eq] using horizontal_derivative (hasDerivAt_id (complexPoint x y))
  exact h.hasFDerivAt.comp_hasDerivAt x hX

private theorem oddCosetPullback_horizontal_floquet (f : OddSmoothCompactCore) (q : levelFourRightCoset)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    oddCosetPullback f q (horizontalUpperPoint (x + 4) hy) =
      periodFourPhase * oddCosetPullback f q (horizontalUpperPoint x hy) := by
  let a := cellRepresentative (CongruenceSubgroup.Gamma0 4) q
  have hEq (u : ℝ) : oddCosetPullback f q (horizontalUpperPoint u hy) =
      cuspHorizontalProfile (f : ℂ → ℂ) a u y := by
    rw [cuspHorizontalProfile, ofComplex_apply_of_im_pos (by simpa only [complexPoint_im] using hy)]
    rw [oddCosetPullback_coe]
    unfold oddCosetChart cuspOddProfile a horizontalUpperPoint
    rw [div_eq_mul_inv, mul_comm]
  rw [hEq, hEq]
  exact cuspHorizontalProfile_floquet f.2.1 a x y hy

theorem horizontal_derivative_norm_sq_le_covariant (F : ℂ → ℂ) (z : ℍ) :
    ‖fderiv ℝ F (z : ℂ) 1‖ ^ 2 ≤ (2 / z.im ^ 2) * (maassCovariantEnergy F z + ‖F z‖ ^ 2) := by
  let D := fderiv ℝ F (z : ℂ) 1
  let A := maassCovariantValue F z 1
  let B := (Complex.I / 4) * F z
  have hEq : (z.im : ℂ) * D = A - B := by
    unfold A B D maassCovariantValue
    simp only [Complex.one_re, Complex.ofReal_one, mul_one, add_sub_cancel_right]
  have hNorm : ‖(z.im : ℂ) * D‖ ^ 2 = z.im ^ 2 * ‖D‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.im_pos, mul_pow]
  have hB₀ : ‖(Complex.I / 4 : ℂ)‖ = (1 : ℝ) / 4 := by
    rw [norm_div, Complex.norm_I]
    norm_num
  have hB : ‖B‖ ^ 2 ≤ ‖F z‖ ^ 2 := by
    unfold B
    rw [norm_mul, hB₀, mul_pow]
    nlinarith only [sq_nonneg ‖F z‖]
  have hDiff : ‖A - B‖ ^ 2 ≤ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    calc
      _ ≤ (‖A‖ + ‖B‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le A B) 2
      _ ≤ _ := by nlinarith only [sq_nonneg (‖A‖ - ‖B‖)]
  rw [← hEq, hNorm] at hDiff
  change ‖D‖ ^ 2 ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos z.im_pos)).2
  change ‖D‖ ^ 2 * z.im ^ 2 ≤ 2 * ((‖A‖ ^ 2 + ‖maassCovariantValue F z Complex.I‖ ^ 2) + ‖F z‖ ^ 2)
  nlinarith only [hDiff, hB, sq_nonneg ‖maassCovariantValue F z Complex.I‖]

def oddCosetChartTotalEnergy (f : OddSmoothCompactCore) (z : ℍ) : ℝ :=
  oddCosetChartEnergyAt f z + oddCosetChartMassAt (f : ℂ → ℂ) z

theorem continuous_oddCosetChartTotalEnergy (f : OddSmoothCompactCore) :
    Continuous (oddCosetChartTotalEnergy f) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  unfold oddCosetChartTotalEnergy oddCosetChartEnergyAt oddCosetChartMassAt
  apply Continuous.add
  · exact continuous_finsetSum _ (fun q _ => oddCosetPullback_energy_continuous f q)
  · apply continuous_finsetSum
    intro q _
    simpa only [oddCosetPullback_coe] using ((oddCosetPullback_continuous f q).norm.pow 2)

theorem oddCosetChartTotalEnergy_invariant (f : OddSmoothCompactCore) (g : SL(2, ℤ)) (z : ℍ) :
    oddCosetChartTotalEnergy f (g • z) = oddCosetChartTotalEnergy f z := by
  unfold oddCosetChartTotalEnergy
  rw [oddCosetChartEnergyAt_invariant, oddCosetChartMassAt_invariant f.2.1]

theorem oddCosetChart_horizontal_mass_le (f : OddSmoothCompactCore) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + 1, oddCosetChartMassAt (f : ℂ → ℂ) (horizontalUpperPoint x hy)) ≤
      (32 / ‖periodFourPhase - 1‖ ^ 2 / y ^ 2) *
        ∫ x in a..a + 1, oddCosetChartTotalEnergy f (horizontalUpperPoint x hy) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  let U := fun x => horizontalUpperPoint x hy
  let F : levelFourRightCoset → ℝ → ℂ := fun q x => oddCosetPullback f q (U x)
  let D : levelFourRightCoset → ℝ → ℂ := fun q x => fderiv ℝ (oddCosetPullback f q) (U x : ℂ) 1
  let E : ℝ → ℝ := fun x => (2 / y ^ 2) * oddCosetChartTotalEnergy f (U x)
  have hD (q : levelFourRightCoset) (x : ℝ) : HasDerivAt (F q) (D q x) x :=
    oddCosetPullback_hasDerivAt f q x hy
  have hDc (q : levelFourRightCoset) : Continuous (D q) :=
    (oddCosetPullback_directional_continuous f q 1).comp (continuous_horizontalUpperPoint hy)
  have hFl (q : levelFourRightCoset) (x : ℝ) : F q (x + 4) = periodFourPhase * F q x :=
    oddCosetPullback_horizontal_floquet f q x hy
  have hEc : Continuous E :=
    continuous_const.mul ((continuous_oddCosetChartTotalEnergy f).comp (continuous_horizontalUpperPoint hy))
  have hEp : Function.Periodic E 1 := by
    intro x
    change (2 / y ^ 2) * oddCosetChartTotalEnergy f (horizontalUpperPoint (x + 1) hy) =
      (2 / y ^ 2) * oddCosetChartTotalEnergy f (horizontalUpperPoint x hy)
    rw [← T_horizontalUpperPoint, oddCosetChartTotalEnergy_invariant]
  have hE (x : ℝ) : (∑ q, ‖D q x‖ ^ 2) ≤ E x := by
    calc
      _ ≤ ∑ q : levelFourRightCoset, (2 / y ^ 2) *
          (maassCovariantEnergy (oddCosetPullback f q) (U x) + ‖F q x‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro q _
        simpa only [F, D, U, horizontalUpperPoint_im] using
          horizontal_derivative_norm_sq_le_covariant (oddCosetPullback f q) (U x)
      _ = _ := by
        unfold E oddCosetChartTotalEnergy oddCosetChartEnergyAt oddCosetChartMassAt F
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [oddCosetPullback_coe]
  have h := floquet_family_strip_norm_sq_le periodFourPhase_ne_one hD hDc hFl hEc hEp hE a
  dsimp only [F, E, U] at h
  simp only [oddCosetPullback_coe] at h
  rw [intervalIntegral.integral_const_mul] at h
  change (∫ x in a..a + 1, ∑ q : levelFourRightCoset,
    ‖oddCosetChart (f : ℂ → ℂ) q (horizontalUpperPoint x hy)‖ ^ 2) ≤ _
  convert h using 1 <;> ring

end
end ManuscriptAudit.Paper8OddMaassHorizontalPoincare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassHorizontalPoincare.oddCosetChart_horizontal_mass_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
