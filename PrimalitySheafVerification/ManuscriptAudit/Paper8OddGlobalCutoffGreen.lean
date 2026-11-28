import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PrimalitySheafVerification.ManuscriptAudit.Paper8CompactCurrentGreen
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCutoffFlux

/-! The genuine odd Maass current has zero total cutoff curl and an exact global energy identity. -/

namespace ManuscriptAudit.Paper8OddGlobalCutoffGreen

open Filter Function Set MeasureTheory UpperHalfPlane ModularForm MaassLaplacian
open Paper8ActualEtaSquaredModularity Paper8MaassWirtinger Paper8MaassCurlCalculus
open Paper8MaassTraceCurl Paper8EtaCosetMass Paper8CompactCurrentGreen
open Paper8EtaCriticalOddVanishing Paper8NegativeHalfMaassFactorization
open Paper8MaassCriticalHolomorphic Paper8MaassAdjointHolomorphic
open Paper8MaassGaugeDerivative Paper8MaassGaugeCurrent Paper8MaassCriticalFlux
open Paper8MaassCutoffDerivative Paper8MaassCutoffTaper Paper8MaassCutoffFlux
open Paper8ModularHeightCutoff Paper8CurvedCurrentGreen
open scoped MatrixGroups ModularForm Topology ContDiff

noncomputable section

local notation "Γ₄" => CongruenceSubgroup.Gamma0 4

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem contDiffOn_to_differentiableAt {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im}) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℝ F w :=
  ((hF w hw).contDiffAt (isOpen_upper.mem_nhds hw)).differentiableAt (by norm_num)

private theorem ofComplex_coe (z : ℍ) : ofComplex (z : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos z.im_pos]

theorem complexCutoff_coe (Y : ℝ) (z : ℍ) : complexCutoff Y z = (modularCutoff Y z : ℂ) := by
  rw [complexCutoff, ofComplex_coe]

theorem cutoffFlux_zero_above {Y : ℝ} (hY : 0 < Y) (F G : ℂ → ℂ) (z : ℍ)
    (hz : 2 * Y < maximumHeight z) : cutoffFlux Y F G z = 0 := by
  simp [cutoffFlux, complexCutoff_coe, modularCutoff, taper_eq_zero hY hz.le]

theorem cutoffFlux_contDiffOn_of_partner {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hAdjGauge : ContDiffOn ℝ 1 (fun w => ModularForm.eta w * adjointPartner G w) {w : ℂ | 0 < w.im}) :
    ContDiffOn ℝ 1 (cutoffFlux Y F G) {w : ℂ | 0 < w.im} := by
  let U : Set ℂ := {w : ℂ | 0 < w.im}
  have hEtaC : DifferentiableOn ℂ ModularForm.eta U := fun w hw =>
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw).differentiableWithinAt
  have hEta : ContDiffOn ℝ 1 ModularForm.eta U :=
    (hEtaC.contDiffOn isOpen_upper).restrict_scalars ℝ
  intro w hw
  let z : ℍ := ⟨w, hw⟩
  have hN := isOpen_upper.mem_nhds hw
  have hPow : ContDiffAt ℝ 1 (fun t : ℝ => t ^ (1 / 4 : ℝ)) w.im :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hw)
  have hHeight : ContDiffAt ℝ 1 (fun v : ℂ => ((v.im ^ (1 / 4 : ℝ) : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w
      (hPow.comp w Complex.imCLM.contDiff.contDiffAt)
  have hConj : ContDiff ℝ 1 (starRingEnd ℂ : ℂ → ℂ) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff
  have hGauge : ContDiffAt ℝ 1 complexGauge w :=
    hHeight.mul (hConj.contDiffAt.comp w ((hEta w hw).contDiffAt hN))
  have hGaugeNe : complexGauge w ≠ 0 := by
    change complexGauge z ≠ 0
    rw [complexGauge_coe]
    exact Paper8MaassEtaGauge.etaGauge_ne_zero z
  have hRatio : ContDiffAt ℝ 1 (complexGaugeRatio F) w := by
    unfold complexGaugeRatio
    simp only [div_eq_mul_inv]
    change ContDiffAt ℝ 1 (F * complexGauge⁻¹) w
    exact ((hF w hw).contDiffAt hN).mul (hGauge.inv hGaugeNe)
  have hChiR : ContDiffAt ℝ 1 (fun v : ℂ => modularCutoff Y (ofComplex v)) w :=
    ((modularCutoff_real_smooth hY).of_le (by simp) w hw).contDiffAt hN
  have hChi : ContDiffAt ℝ 1 (complexCutoff Y) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hChiR
  have hJ : ContDiffAt ℝ 1 (fluxCurrent F G) w :=
    (hConj.contDiffAt.comp w hRatio).mul ((hAdjGauge w hw).contDiffAt hN)
  exact ((hChi.pow 2).mul hJ).contDiffWithinAt

theorem cutoffFlux_contDiffOn {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0) :
    ContDiffOn ℝ 1 (cutoffFlux Y F G) {w : ℂ | 0 < w.im} := by
  apply cutoffFlux_contDiffOn_of_partner hY hF
  exact ((adjointGaugeProduct_differentiableOn hG hAdj).contDiffOn isOpen_upper).restrict_scalars ℝ

theorem cutoffFlux_contDiffOn_of_realSmooth {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ 1 G {w : ℂ | 0 < w.im}) :
    ContDiffOn ℝ 1 (cutoffFlux Y F G) {w : ℂ | 0 < w.im} := by
  apply cutoffFlux_contDiffOn_of_partner hY hF
  let U : Set ℂ := {w : ℂ | 0 < w.im}
  have hEtaC : DifferentiableOn ℂ ModularForm.eta U := fun w hw =>
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw).differentiableWithinAt
  have hEta : ContDiffOn ℝ 1 ModularForm.eta U :=
    (hEtaC.contDiffOn isOpen_upper).restrict_scalars ℝ
  intro w hw
  have hN := isOpen_upper.mem_nhds hw
  have hPow : ContDiffAt ℝ 1 (fun t : ℝ => t ^ (-(3 / 4 : ℝ))) w.im :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hw)
  have hHeight : ContDiffAt ℝ 1 (fun v : ℂ => ((v.im ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (hPow.comp w Complex.imCLM.contDiff.contDiffAt)
  exact (((hEta w hw).contDiffAt hN).mul (hHeight.mul ((hG w hw).contDiffAt hN))).contDiffWithinAt

theorem cutoffFlux_slash (Y : ℝ) {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (g : SL(2, ℤ)) (hg : g ∈ Γ₄) :
    (fun z : ℍ => cutoffFlux Y F G z) ∣[(2 : ℤ)] g =
      fun z : ℍ => cutoffFlux Y F G z := by
  funext z
  have h := currentCoefficient_pullback_eq hLaw hF (⟨g, hg⟩ : Γ₄) z
  change currentCoefficient F (g • z) * deriv (fractionalLinear g) z = currentCoefficient F z at h
  rw [(fractionalLinear_hasDerivAt g z).deriv] at h
  rw [SL_slash_apply, ← denominator_eq, zpow_neg, zpow_ofNat]
  change cutoffFlux Y F G (g • z : ℍ) * (denominator g z ^ 2)⁻¹ = cutoffFlux Y F G z
  simp only [cutoffFlux, complexCutoff_coe, modularCutoff_invariant, fluxCurrent_coe_eq hF hRaise]
  rw [mul_assoc ((modularCutoff Y z : ℂ) ^ 2) _, mul_assoc (2 * Complex.I) _, h]

theorem integral_oddCutoffFlux_zero {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0) :
    (∫ z in cosetCells Γ₄ ModularGroup.fd, weightedCurl (cutoffFlux Y F G) z) = 0 := by
  apply integral_compact_current_zero Γ₄ ?_ _ (B := 2 * Y) (by linarith)
    (cutoffFlux_contDiffOn hY hF hG hAdj)
    (cutoffFlux_zero_above (by linarith) F G)
    (cutoffFlux_slash Y hLaw (fun _ hw => contDiffOn_to_differentiableAt hF hw) hRaise)
  change ((((-1 : SL(2, ℤ)).1 1 0 : ℤ) : ZMod 4) = 0)
  have hz : (-1 : SL(2, ℤ)).1 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Matrix.one_apply]
  rw [hz, Int.cast_zero]

def cutoffEnergy (Y : ℝ) (G : ℂ → ℂ) (z : ℍ) : ℝ := (modularCutoff Y z * ‖G z‖) ^ 2

def weightedCutoffError (Y : ℝ) (F G : ℂ → ℂ) (z : ℍ) : ℂ :=
  (z.im ^ 2 : ℝ) * cutoffError Y F G z

theorem weightedCurl_cutoffFlux {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0) (z : ℍ) :
    weightedCurl (cutoffFlux Y F G) z = -(cutoffEnergy Y G z : ℂ) + weightedCutoffError Y F G z := by
  have h := cutoffFlux_curl hY hF hG hRaise hAdj z.re z.im z.im_pos
  have hRaise' := hRaise z.re z.im z.im_pos
  have hPoint : complexPoint z.re z.im = (z : ℂ) := Complex.re_add_im z
  change complexCurl (cutoffFlux Y F G) (complexPoint z.re z.im) = _ at h
  rw [← hRaise', hPoint, complexCutoff_coe] at h
  unfold weightedCurl cutoffEnergy weightedCutoffError
  rw [h]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne'] <;> ring

theorem integral_odd_cutoff_energy {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0) :
    let S := cosetCells Γ₄ ModularGroup.fd
    (∫ z in S, cutoffEnergy Y G z) = (∫ z in S, weightedCutoffError Y F G z).re := by
  let J := cutoffFlux Y F G
  let S := cosetCells Γ₄ ModularGroup.fd
  let A := cutoffEnergy Y G
  let E := weightedCutoffError Y F G
  have hdF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w := fun _ => contDiffOn_to_differentiableAt hF
  have hPoint (z : ℍ) : weightedCurl J z = -(A z : ℂ) + E z :=
    weightedCurl_cutoffFlux hY hdF hG hRaise hAdj z
  have hChi : Continuous (modularCutoff Y) := by
    have h := (modularCutoff_real_smooth hY).continuousOn.comp_continuous UpperHalfPlane.continuous_coe
      (fun z => z.im_pos)
    have hEq : (fun w : ℂ => modularCutoff Y (ofComplex w)) ∘
        ((↑) : ℍ → ℂ) = modularCutoff Y :=
      funext fun z => congrArg (modularCutoff Y) (ofComplex_coe z)
    rwa [hEq] at h
  have hGc : Continuous (fun z : ℍ => G z) := by
    have h : ContinuousOn G {w : ℂ | 0 < w.im} :=
      (show DifferentiableOn ℝ G {w : ℂ | 0 < w.im} from
        fun w hw => (hG w hw).differentiableWithinAt).continuousOn
    exact h.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  have hAs : ∀ z : ℍ, 2 * Y < maximumHeight z → A z = 0 := fun z hz => by
    simp [A, cutoffEnergy, modularCutoff, taper_eq_zero (by linarith : 0 < Y) hz.le]
  have hA : IntegrableOn A S :=
    integrableOn_cusp_support Γ₄ A (((hChi.mul hGc.norm).pow 2)) hAs
  have hAc : IntegrableOn (fun z : ℍ => (A z : ℂ)) S := Complex.ofRealCLM.integrable_comp hA
  have hCurl : IntegrableOn (weightedCurl J) S :=
    integrableOn_weightedCurl Γ₄ J (cutoffFlux_contDiffOn hY hF hG hAdj)
      (cutoffFlux_zero_above (by linarith) F G)
  have hInt : (∫ z in S, weightedCurl J z) = 0 := integral_oddCutoffFlux_zero hY hLaw hF hG hRaise hAdj
  calc
    _ = ((↑(∫ z in S, A z) : ℂ)).re := (Complex.ofReal_re _).symm
    _ = (∫ z in S, (A z : ℂ)).re := by rw [integral_complex_ofReal]
    _ = (∫ z in S, weightedCurl J z + (A z : ℂ)).re := by rw [integral_add hCurl hAc, hInt, zero_add]
    _ = _ := congrArg Complex.re (integral_congr_ae (Eventually.of_forall (fun z => by
      change weightedCurl J z + (A z : ℂ) = E z
      rw [hPoint]
      ring)))

end
end ManuscriptAudit.Paper8OddGlobalCutoffGreen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGlobalCutoffGreen.integral_oddCutoffFlux_zero,
      ``ManuscriptAudit.Paper8OddGlobalCutoffGreen.integral_odd_cutoff_energy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
