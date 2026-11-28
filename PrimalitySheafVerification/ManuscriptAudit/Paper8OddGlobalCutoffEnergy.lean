import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCutoffGreen
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularCuspTail
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassStripFubini

/-! On the actual level-four domain, the compact Maass energy is bounded by the shrinking cusp mass. -/

namespace ManuscriptAudit.Paper8OddGlobalCutoffEnergy

open Filter Function Set MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8EtaCosetMass Paper8MaassTraceCurl Paper8ModularHeightCutoff Paper8ModularCuspTail
open Paper8CompactCurrentGreen Paper8OddGlobalCutoffGreen Paper8MaassCutoffFlux
open Paper8MaassCutoffTaper Paper8MaassCutoffDerivative Paper8MaassStripFubini
open Paper8EtaCriticalOddVanishing Paper8NegativeHalfMaassFactorization Paper8MaassCriticalHolomorphic
open scoped MatrixGroups ENNReal Topology ContDiff

noncomputable section

def levelFourCells : Set ℍ := cosetCells (CongruenceSubgroup.Gamma0 4) ModularGroup.fd

theorem measurable_levelFourCells : MeasurableSet levelFourCells := by
  letI := FiniteIndexWeightZeroCosets.rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  apply MeasurableSet.iUnion
  intro q
  exact (measurableEmbedding_const_smul (cellRepresentative (CongruenceSubgroup.Gamma0 4) q :
    GL (Fin 2) ℝ)).measurableSet_image.mpr ModularGroup.isClosed_fd.measurableSet

private theorem realCutoff_nonneg (Y : ℝ) (z : ℍ) : 0 ≤ modularCutoff Y z := by
  unfold modularCutoff taper baseTaper
  exact sub_nonneg.mpr (Real.smoothTransition.le_one _)

private theorem differentiableAt_of_contDiffOn {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im}) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℝ F w := by
  have hU : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
  exact ((hF w hw).contDiffAt (hU.mem_nhds hw)).differentiableAt (by norm_num)

private theorem continuous_of_differentiableAt {F : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w) :
    Continuous (fun z : ℍ => F z) := by
  have hC : ContinuousOn F {w : ℂ | 0 < w.im} :=
    (show DifferentiableOn ℝ F {w : ℂ | 0 < w.im} from
      fun w hw => (hF w hw).differentiableWithinAt).continuousOn
  exact hC.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

theorem cutoffEnergy_integrableOn {Y : ℝ} (hY : 2 < Y) {G : ℂ → ℂ}
    (hG : Continuous (fun z : ℍ => G z)) : IntegrableOn (cutoffEnergy Y G) levelFourCells := by
  have hChi : Continuous (modularCutoff Y) := by
    have h := (modularCutoff_real_smooth hY).continuousOn.comp_continuous UpperHalfPlane.continuous_coe
      (fun z => z.im_pos)
    convert h using 1
    funext z
    rw [ofComplex_apply_of_im_pos z.im_pos]
  apply integrableOn_cusp_support (CongruenceSubgroup.Gamma0 4) (cutoffEnergy Y G) ((hChi.mul hG.norm).pow 2)
  intro z hz
  simp [cutoffEnergy, modularCutoff, taper_eq_zero (by linarith : 0 < Y) hz.le]

theorem cutoffError_weighted_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 2, ∀ N < Y, ∀ (F G : ℂ → ℂ) (z : ℍ),
      (weightedCutoffError Y F G z).re ≤
        (cutoffEnergy Y G z +
          C ^ 2 * {u : ℍ | N < maximumHeight u}.indicator (fun u => ‖F u‖ ^ 2) z) / 2 := by
  obtain ⟨C, hC, hErr⟩ := cutoffError_uniform
  refine ⟨C, hC, fun Y hY N hNY F G z => ?_⟩
  by_cases hz : N < maximumHeight z
  · rw [indicator_of_mem (show z ∈ {u : ℍ | N < maximumHeight u} from hz)]
    have hBound := hErr Y hY F G z
    rw [complexCutoff_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realCutoff_nonneg Y z)] at hBound
    have hI : ‖weightedCutoffError Y F G z‖ =
        z.im ^ 2 * ‖cutoffError Y F G z‖ := by
      unfold weightedCutoffError
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z.im)]
    have hMul : z.im ^ 2 * ‖cutoffError Y F G z‖ ≤
        (C * ‖F z‖) * (modularCutoff Y z * ‖G z‖) := by
      have hIm : 0 < z.im ^ 2 := sq_pos_of_pos z.im_pos
      have h := (le_div_iff₀ hIm).mp hBound
      convert h using 1 <;> ring
    have hYoung := sq_nonneg (C * ‖F z‖ - modularCutoff Y z * ‖G z‖)
    calc
      _ ≤ ‖weightedCutoffError Y F G z‖ := Complex.re_le_norm _
      _ ≤ _ := by
        rw [hI]
        apply hMul.trans
        unfold cutoffEnergy
        nlinarith
  · have hZ : maximumHeight z < Y := (le_of_not_gt hz).trans_lt hNY
    have hE := cutoffError_zero_below hY F G z hZ
    rw [indicator_of_notMem (show z ∉ {u : ℍ | N < maximumHeight u} from hz)]
    simp only [weightedCutoffError, hE, mul_zero, Complex.zero_re, add_zero]
    exact div_nonneg (sq_nonneg _) (by norm_num)

theorem normSquare_integrableOn_of_mass {F : ℂ → ℂ}
    (hF : Continuous (fun z : ℍ => F z))
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    IntegrableOn (fun z : ℍ => ‖F z‖ ^ 2) levelFourCells := by
  constructor
  · exact (hF.norm.pow 2).aestronglyMeasurable
  · exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z : ℍ => sq_nonneg ‖F z‖))).2 hMass

theorem cutoffEnergy_le_cusp_tail {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 2, ∀ N < Y,
      (∫ z in levelFourCells, cutoffEnergy Y G z) ≤
        C ^ 2 * (∫ z in levelFourCells ∩ {u : ℍ | N < maximumHeight u}, ‖F z‖ ^ 2) := by
  obtain ⟨C, hC, hBound⟩ := cutoffError_weighted_bound
  refine ⟨C, hC, fun Y hY N hNY => ?_⟩
  let A := cutoffEnergy Y G
  let E := weightedCutoffError Y F G
  let T : Set ℍ := {u : ℍ | N < maximumHeight u}
  let P : ℍ → ℝ := T.indicator (fun z : ℍ => ‖F z‖ ^ 2)
  let S := levelFourCells
  have hT : MeasurableSet T := (isOpen_height_above N).measurableSet
  have hdF (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℝ F w := differentiableAt_of_contDiffOn hF hw
  have hA : IntegrableOn A S := cutoffEnergy_integrableOn hY (continuous_of_differentiableAt hG)
  have hAc : IntegrableOn (fun z : ℍ => (A z : ℂ)) S := Complex.ofRealCLM.integrable_comp hA
  have hP : IntegrableOn P S :=
    (normSquare_integrableOn_of_mass (continuous_of_differentiableAt hdF) hMass).indicator hT
  have hJ : IntegrableOn (weightedCurl (cutoffFlux Y F G)) S :=
    integrableOn_weightedCurl (CongruenceSubgroup.Gamma0 4) _ (cutoffFlux_contDiffOn hY hF hG hAdj)
      (cutoffFlux_zero_above (by linarith) F G)
  have hE : IntegrableOn E S := (hJ.add hAc).congr (Eventually.of_forall (fun z => by
    change weightedCurl (cutoffFlux Y F G) z + (A z : ℂ) = E z
    rw [weightedCurl_cutoffFlux hY hdF hG hRaise hAdj]
    change -(A z : ℂ) + E z + (A z : ℂ) = E z
    ring))
  have hEr : IntegrableOn (fun z : ℍ => (E z).re) S := Complex.reCLM.integrable_comp hE
  have hB : IntegrableOn (fun z => (A z + C ^ 2 * P z) / 2) S :=
    (hA.add (hP.const_mul _)).div_const _
  have hI := integral_odd_cutoff_energy hY hLaw hF hG hRaise hAdj
  change (∫ z in S, A z) = (∫ z in S, E z).re at hI
  rw [← integral_re hE] at hI
  have hMon := integral_mono hEr hB (hBound Y hY N hNY F G)
  rw [← hI, integral_div, integral_add hA (hP.const_mul _), integral_const_mul] at hMon
  have hPInt : (∫ z in S, P z) = ∫ z in S ∩ T, ‖F z‖ ^ 2 := by
    rw [show P = T.indicator (fun z : ℍ => ‖F z‖ ^ 2) from rfl, integral_indicator hT,
      Measure.restrict_restrict hT, inter_comm T S]
  rw [hPInt] at hMon
  linarith

theorem cutoffEnergy_tendsto_zero {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    Tendsto (fun n : ℕ => ∫ z in levelFourCells, cutoffEnergy ((n : ℝ) + 3) G z) atTop (𝓝 0) := by
  let T (n : ℕ) : Set ℍ := levelFourCells ∩ {u : ℍ | (n : ℝ) < maximumHeight u}
  have hTail := lintegral_cusp_tail_tendsto_zero measurable_levelFourCells hMass
  have hLim : Tendsto (fun n : ℕ => ∫ z in T n, ‖F z‖ ^ 2) atTop (𝓝 0) := by
    have hTo := (ENNReal.continuousAt_toReal (x := 0) (by simp)).tendsto.comp hTail
    have hFc := continuous_of_differentiableAt
      (fun _ hw => differentiableAt_of_contDiffOn hF hw)
    have hEq (n : ℕ) : (∫ z in T n, ‖F z‖ ^ 2) =
        (∫⁻ z in T n, normSquareDensity F z).toReal := by
      exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun z : ℍ => sq_nonneg ‖F z‖))
        ((hFc.norm.pow 2).aestronglyMeasurable)
    simpa only [Function.comp_def, ENNReal.toReal_zero, ← hEq] using hTo
  obtain ⟨C, _, hBound⟩ := cutoffEnergy_le_cusp_tail hLaw hF hG hRaise hAdj hMass
  have hHigh : Tendsto (fun n : ℕ => C ^ 2 * (∫ z in T n, ‖F z‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C ^ 2)).mul hLim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hHigh
  · intro n
    exact integral_nonneg (fun z => sq_nonneg _)
  · intro n
    exact hBound ((n : ℝ) + 3) (by positivity) (n : ℝ) (by linarith)

end
end ManuscriptAudit.Paper8OddGlobalCutoffEnergy

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddGlobalCutoffEnergy.cutoffEnergy_tendsto_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
