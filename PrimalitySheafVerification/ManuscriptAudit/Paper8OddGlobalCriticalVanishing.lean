import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Measure.OpenPos
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCutoffEnergy
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGlobalStripEnergy

/-! Finite genuine mass forces the entire critical odd raising field and the original form to vanish. -/

namespace ManuscriptAudit.Paper8OddGlobalCriticalVanishing

open Filter Set MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8EtaCosetMass Paper8EtaCosetBoundary FiniteIndexWeightZeroCosets
open Paper8EtaPeterssonMass (translate)
open Paper8MaassWirtinger Paper8MaassStripFubini Paper8ModularHeightCutoff Paper8ModularCuspTail
open Paper8OddGlobalCutoffGreen Paper8OddGlobalCutoffEnergy Paper8MaassCutoffTaper
open Paper8EtaCriticalOddVanishing Paper8NegativeHalfMaassFactorization Paper8MaassCriticalHolomorphic
open Paper8MaassGaugeDerivative Paper8MaassGaugeRaising Paper8MaassGlobalStripEnergy
open scoped MatrixGroups ENNReal NNReal Topology

noncomputable section

local notation "Γ₄" => CongruenceSubgroup.Gamma0 4

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem complexProfile_continuous {G : ℂ → ℂ}
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w) :
    Continuous (fun z : ℍ => G z) := by
  have h : ContinuousOn G {w : ℂ | 0 < w.im} :=
    (show DifferentiableOn ℝ G {w : ℂ | 0 < w.im} from
      fun w hw => (hG w hw).differentiableWithinAt).continuousOn
  exact h.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

theorem levelFourOpenCells_isOpen : IsOpen (cosetCells Γ₄ ModularGroup.fdo) := by
  apply isOpen_iUnion
  intro q
  let g := cellRepresentative Γ₄ q
  have h : translate g ModularGroup.fdo = (fun z : ℍ => g⁻¹ • z) ⁻¹' ModularGroup.fdo := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change g⁻¹ • (g • w) ∈ ModularGroup.fdo
      rwa [inv_smul_smul]
    · intro hz
      exact ⟨g⁻¹ • z, hz, smul_inv_smul g z⟩
  change IsOpen (translate g ModularGroup.fdo)
  rw [h]
  apply ModularGroup.isOpen_fdo.preimage
  change Continuous (fun z : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ (g⁻¹) • z)
  exact continuous_const_smul _

theorem actualVolume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let D (z : ℍ) : ℝ≥0∞ := ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)
  haveI : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap (volume : Measure ℂ) UpperHalfPlane.isOpenEmbedding_coe
  have hM : Measurable D := by
    have hIm : Measurable (fun z : ℍ => (NNReal.mk z.im z.im_pos.le : ℝ≥0)) :=
      measurable_coe_nnreal_real_iff.mp UpperHalfPlane.continuous_im.measurable
    exact ((measurable_const.div hIm).pow_const 2).coe_nnreal_ennreal
  have hD (z : ℍ) : D z ≠ 0 := by
    have hIm : (NNReal.mk z.im z.im_pos.le : ℝ≥0) ≠ 0 := fun h =>
      z.im_ne_zero (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (div_ne_zero one_ne_zero hIm))
  have hVol : (volume : Measure ℍ) = μ.withDensity D := UpperHalfPlane.volume_def
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := μ)
  rw [hVol]
  exact withDensity_absolutelyContinuous' hM.aemeasurable (Eventually.of_forall hD)

theorem raisingField_ae_zero_on_cells {G : ℂ → ℂ}
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hLim : Tendsto (fun n : ℕ => ∫ z in levelFourCells, cutoffEnergy ((n : ℝ) + 3) G z) atTop (𝓝 0)) :
    (fun z : ℍ => G z) =ᵐ[(volume : Measure ℍ).restrict levelFourCells] 0 := by
  let S := levelFourCells
  let μ := (volume : Measure ℍ).restrict S
  let U (n : ℕ) : Set ℍ := {z | maximumHeight z ≤ (n : ℝ)}
  let Q (z : ℍ) := ‖G z‖ ^ 2
  have hGc := complexProfile_continuous hG
  have hQ : Measurable Q := (hGc.norm.pow 2).measurable
  have hU (n : ℕ) : MeasurableSet (U n) := by
    have h : U n = {z : ℍ | (n : ℝ) < maximumHeight z}ᶜ := by
      ext z
      change maximumHeight z ≤ (n : ℝ) ↔ ¬(n : ℝ) < maximumHeight z
      exact not_lt.symm
    rw [h]
    exact (isOpen_height_above (n : ℝ)).measurableSet.compl
  have hPoint (n m : ℕ) (hm : n ≤ m) (z : ℍ) :
      (U n).indicator Q z ≤ cutoffEnergy ((m : ℝ) + 3) G z := by
    by_cases hz : z ∈ U n
    · rw [indicator_of_mem hz]
      have hM : maximumHeight z ≤ (m : ℝ) + 3 := by
        have hh : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        change maximumHeight z ≤ (n : ℝ) at hz
        linarith
      unfold cutoffEnergy modularCutoff Q
      rw [taper_eq_one (by positivity : 0 < (m : ℝ) + 3) hM, one_mul]
    · rw [indicator_of_notMem hz]
      exact sq_nonneg _
  have hAE (n : ℕ) : (U n).indicator Q =ᵐ[μ] 0 := by
    have hInt' : Integrable (cutoffEnergy ((n : ℝ) + 3) G) μ :=
      cutoffEnergy_integrableOn (by
        have hCast : 0 ≤ (n : ℝ) := by positivity
        linarith) hGc
    have hInt : Integrable ((U n).indicator Q) μ :=
      hInt'.mono' ((hQ.indicator (hU n)).aestronglyMeasurable) (Eventually.of_forall (fun z => by
        have h : 0 ≤ (U n).indicator Q z := indicator_nonneg (fun _ _ => sq_nonneg _) _
        simpa only [Real.norm_eq_abs, abs_of_nonneg h] using hPoint n n le_rfl z))
    have hNN : 0 ≤ᵐ[μ] (U n).indicator Q :=
      Eventually.of_forall (fun z => indicator_nonneg (fun _ _ => sq_nonneg _) _)
    have hLe : (∫ z, (U n).indicator Q z ∂μ) ≤ 0 := by
      apply ge_of_tendsto hLim
      filter_upwards [eventually_ge_atTop n] with m hm
      have hCutoff : 2 < (m : ℝ) + 3 := by
        have hCast : 0 ≤ (m : ℝ) := by positivity
        linarith
      exact integral_mono hInt (cutoffEnergy_integrableOn hCutoff hGc) (hPoint n m hm)
    exact (integral_eq_zero_iff_of_nonneg_ae hNN hInt).mp
      (le_antisymm hLe (integral_nonneg_of_ae hNN))
  have hAll : ∀ᵐ z ∂μ, ∀ n : ℕ, (U n).indicator Q z = 0 := ae_all_iff.2 hAE
  filter_upwards [hAll] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (maximumHeight z)
  have hzU : z ∈ U n := hn.le
  have h0 := hz n
  rw [indicator_of_mem hzU] at h0
  change ‖G z‖ ^ 2 = 0 at h0
  have hNorm : ‖G z‖ = 0 := by nlinarith [sq_nonneg ‖G z‖]
  simpa only [Pi.zero_apply] using norm_eq_zero.mp hNorm

private theorem raisingField_zero_smul {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (g : Γ₄) (z : ℍ) (hz : G z = 0) : G ((g : SL(2, ℤ)) • z : ℍ) = 0 := by
  have hFormula (u : ℍ) : G u =
      2 * Complex.I * (u.im : ℂ) * complexGauge u * derivativeZ (complexGaugeRatio F) u := by
    have hPoint : complexPoint u.re u.im = (u : ℂ) := Complex.re_add_im u
    have hDiff : DifferentiableAt ℝ F (complexPoint u.re u.im) := by
      rw [hPoint]
      exact hF u u.im_pos
    simpa only [hPoint] using (hRaise u.re u.im u.im_pos).trans
      (raising_eq_gauge_derivativeZ u.re u.im u.im_pos hDiff)
  have hGauge : complexGauge z ≠ 0 := by
    rw [complexGauge_coe]
    exact Paper8MaassEtaGauge.etaGauge_ne_zero z
  have hC : (2 : ℂ) * Complex.I * (z.im : ℂ) * complexGauge z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr z.im_ne_zero)) hGauge
  have hD : derivativeZ (complexGaugeRatio F) z = 0 := by
    rw [hFormula] at hz
    exact (mul_eq_zero.mp hz).resolve_left hC
  rw [hFormula, gauge_derivativeZ_transform hLaw hF g z, hD, mul_zero, mul_zero]

theorem raisingField_eq_zero_of_global_mass {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (hMass : (∫⁻ z in levelFourCells, Paper8MaassStripFubini.normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, G z = 0 := by
  letI := actualVolume_isOpenPosMeasure
  let O := cosetCells Γ₄ ModularGroup.fdo
  have hO : IsOpen O := levelFourOpenCells_isOpen
  have hC := complexProfile_continuous hG
  have hLim := cutoffEnergy_tendsto_zero hLaw hF hG hRaise hAdj hMass
  have hAE := raisingField_ae_zero_on_cells hG hLim
  have hRestrict : (volume : Measure ℍ).restrict levelFourCells = volume.restrict O :=
    Measure.restrict_congr_set (closed_cells_ae_eq_open Γ₄)
  rw [hRestrict] at hAE
  have hOpen : EqOn (fun z : ℍ => G z) (fun _ => 0) O :=
    Measure.eqOn_open_of_ae_eq hAE hO hC.continuousOn continuousOn_const
  have hdF (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℝ F w :=
    ((hF w hw).contDiffAt (isOpen_upper.mem_nhds hw)).differentiableAt (by norm_num)
  have hAll : (fun z : ℍ => G z) =ᵐ[(volume : Measure ℍ)] (fun _ => 0) := by
    filter_upwards [open_cells_meet_ae_orbit Γ₄] with z hz
    obtain ⟨g, w, hw, rfl⟩ := hz
    exact raisingField_zero_smul hLaw hdF hRaise g w (hOpen hw)
  intro z
  exact congrFun (Measure.eq_of_ae_eq hAll hC continuous_const) z

theorem odd_critical_form_eq_zero_of_global_mass {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (hMass : (∫⁻ z in levelFourCells, Paper8MaassStripFubini.normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, F z = 0 := by
  have hZero := raisingField_eq_zero_of_global_mass hLaw hF hG hRaise hAdj hMass
  apply odd_maass_raising_kernel_eq_zero_of_global_mass hLaw ?_ ?_ hMass
  · intro w hw
    exact ((hF w hw).contDiffAt (isOpen_upper.mem_nhds hw)).differentiableAt (by norm_num)
  · intro x y hy
    let z : ℍ := ⟨complexPoint x y, by rwa [complexPoint_im]⟩
    exact (hRaise x y hy).symm.trans (hZero z)

end
end ManuscriptAudit.Paper8OddGlobalCriticalVanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGlobalCriticalVanishing.raisingField_eq_zero_of_global_mass,
      ``ManuscriptAudit.Paper8OddGlobalCriticalVanishing.odd_critical_form_eq_zero_of_global_mass] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
