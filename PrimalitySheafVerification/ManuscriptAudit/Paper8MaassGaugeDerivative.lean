import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Congr
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassEtaGauge
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassWirtinger

/-! The actual odd Maass eta-gauge derivative has the exact weight-two denominator factor. -/

namespace ManuscriptAudit.Paper8MaassGaugeDerivative

open Filter Function Set UpperHalfPlane
open Paper8MaassEtaGauge Paper8MaassWirtinger Paper8EtaCriticalOddVanishing
open Paper8ActualEtaSquaredModularity Paper8EtaMaassEigenfunction
open Paper8OddCrossCuspRows (levelCharacter)
open scoped MatrixGroups Topology

noncomputable section

def complexGauge (w : ℂ) : ℂ :=
  (w.im ^ (1 / 4 : ℝ) : ℝ) * (starRingEnd ℂ) (ModularForm.eta w)

theorem complexGauge_coe (z : ℍ) :
    complexGauge z = etaGauge z := by
  simp only [complexGauge, etaGauge, etaMaass, map_mul, Complex.conj_ofReal, UpperHalfPlane.coe_im]

def complexGaugeRatio (F : ℂ → ℂ) (w : ℂ) : ℂ := F w / complexGauge w

theorem complexGaugeRatio_coe (F : ℂ → ℂ) (z : ℍ) :
    complexGaugeRatio F z = gaugeRatio F z := by
  simp only [complexGaugeRatio, gaugeRatio, complexGauge_coe]

theorem complexGauge_differentiableAt (z : ℍ) : DifferentiableAt ℝ complexGauge z := by
  have hHeight : DifferentiableAt ℝ (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ)) z.im :=
    (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl z.im_ne_zero)).ofReal_comp.differentiableAt
  have hI : DifferentiableAt ℝ (fun w : ℂ => w.im) z := Complex.imCLM.differentiableAt
  have hEta : DifferentiableAt ℝ ModularForm.eta z :=
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).restrictScalars ℝ
  exact (hHeight.comp (z : ℂ) hI).mul (Complex.differentiable_conj.differentiableAt.comp _ hEta)

theorem complexGaugeRatio_differentiableAt {F : ℂ → ℂ} (z : ℍ)
    (hF : DifferentiableAt ℝ F z) : DifferentiableAt ℝ (complexGaugeRatio F) z := by
  have hG : complexGauge z ≠ 0 := by rw [complexGauge_coe]; exact etaGauge_ne_zero z
  have hInvC : DifferentiableAt ℂ (fun v : ℂ => v⁻¹) (complexGauge z) :=
    (hasDerivAt_inv hG).differentiableAt
  have hInv : DifferentiableAt ℝ ((fun v : ℂ => v⁻¹) ∘ complexGauge) z :=
    (hInvC.restrictScalars ℝ).comp (z : ℂ) (complexGauge_differentiableAt z)
  unfold complexGaugeRatio
  simp only [div_eq_mul_inv]
  exact hF.mul hInv

theorem gauge_derivativeZ_transform {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    derivativeZ (complexGaugeRatio F) ((g : SL(2, ℤ)) • z : ℍ) =
      ((levelCharacter g : ℂ) * squaredMultiplier (g : SL(2, ℤ))) *
        denominator (g : SL(2, ℤ)) z ^ 2 * derivativeZ (complexGaugeRatio F) z := by
  let a := (g : SL(2, ℤ))
  let c : ℂ := (levelCharacter g : ℂ) * squaredMultiplier a
  let B := complexGaugeRatio F
  have hLawLocal : B ∘ fractionalLinear a =ᶠ[𝓝 (z : ℂ)] (fun w => c * B w) := by
    filter_upwards [Complex.continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds z.im_pos)]
      with w hw
    let u : ℍ := ⟨w, hw⟩
    change B (fractionalLinear a u) = c * B u
    rw [fractionalLinear_eq a u]
    simpa only [B, complexGaugeRatio_coe, c, a] using gaugeRatio_transform hLaw g u
  have hD : derivativeZ (B ∘ fractionalLinear a) z = derivativeZ (fun w => c * B w) z := by
    unfold derivativeZ
    rw [hLawLocal.fderiv_eq (𝕜 := ℝ)]
  have hBz : DifferentiableAt ℝ B z := complexGaugeRatio_differentiableAt z (hF z z.im_pos)
  have hBgz : DifferentiableAt ℝ B (fractionalLinear a z) := by
    rw [fractionalLinear_eq]
    exact complexGaugeRatio_differentiableAt (a • z) (hF _ (a • z : ℍ).im_pos)
  rw [derivativeZ_comp_holomorphic hBgz (fractionalLinear_hasDerivAt a z).differentiableAt,
    (fractionalLinear_hasDerivAt a z).deriv, derivativeZ_const_mul hBz c,
    fractionalLinear_eq] at hD
  change derivativeZ B (a • z : ℍ) = c * denominator a z ^ 2 * derivativeZ B z
  calc
    _ = denominator a z ^ 2 *
        ((denominator a z ^ 2)⁻¹ * derivativeZ B (a • z : ℍ)) := by
      field_simp [denominator_ne_zero a z] <;> ring
    _ = _ := by rw [hD]; ring

end
end ManuscriptAudit.Paper8MaassGaugeDerivative

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassGaugeDerivative.gauge_derivativeZ_transform
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
