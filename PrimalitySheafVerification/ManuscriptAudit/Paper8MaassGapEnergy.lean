import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassNoncriticalCutoff
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCutoffEnergy

/-! The genuine global odd energy estimate at a general shifted Maass eigenvalue. -/

namespace ManuscriptAudit.Paper8MaassGapEnergy

open Filter Function Set MeasureTheory UpperHalfPlane ModularForm MaassLaplacian
open Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization Paper8EtaCriticalOddVanishing
open Paper8MaassTraceCurl Paper8CompactCurrentGreen Paper8MaassCutoffFlux
open Paper8OddGlobalCutoffGreen Paper8OddGlobalCutoffEnergy Paper8MaassNoncriticalCutoff
open Paper8ModularHeightCutoff Paper8ModularCuspTail Paper8MaassStripFubini
open scoped MatrixGroups ModularForm ENNReal Topology

noncomputable section

local notation "Γ₄" => CongruenceSubgroup.Gamma0 4

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem differentiableAt_of_contDiffOn {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    {w : ℂ} (hw : 0 < w.im) : DifferentiableAt ℝ F w :=
  ((hF w hw).contDiffAt (isOpen_upper.mem_nhds hw)).differentiableAt (by norm_num)

private theorem continuous_profile {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im}) :
    Continuous (fun z : ℍ => F z) :=
  hF.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

theorem odd_shifted_cutoff_energy_le_tail {δ : ℝ} {F G : ℂ → ℂ}
    (hLaw : OddMaassLaw F)
    (hF : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ 1 G {w : ℂ | 0 < w.im})
    (hJ : ∀ Y > 2, ContDiffOn ℝ 1 (cutoffFlux Y F G) {w : ℂ | 0 < w.im})
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = (δ : ℂ) * realProfile F x y)
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 2, ∀ N < Y,
      (∫ z in levelFourCells, cutoffEnergy Y G z) -
          2 * δ * (∫ z in levelFourCells, cutoffEnergy Y F z) ≤
        C ^ 2 * ∫ z in levelFourCells ∩ {u : ℍ | N < maximumHeight u}, ‖F z‖ ^ 2 := by
  obtain ⟨C, hC, hBound⟩ := cutoffError_weighted_bound
  refine ⟨C, hC, fun Y hY N hNY => ?_⟩
  let J := cutoffFlux Y F G
  let S := levelFourCells
  let T : Set ℍ := {u : ℍ | N < maximumHeight u}
  let Q := weightedCurl J
  let A := cutoffEnergy Y G
  let B := cutoffEnergy Y F
  let P := T.indicator (fun z : ℍ => ‖F z‖ ^ 2)
  let R (z : ℍ) := (Q z).re + A z - δ * B z
  let W (z : ℍ) := (A z + C ^ 2 * P z) / 2
  have hdF (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℝ F w :=
    differentiableAt_of_contDiffOn hF hw
  have hdG (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℝ G w :=
    differentiableAt_of_contDiffOn hG hw
  have hT : MeasurableSet T := (isOpen_height_above N).measurableSet
  have hSupp : ∀ z : ℍ, 2 * Y < maximumHeight z → J z = 0 :=
    cutoffFlux_zero_above (by linarith) F G
  have hNeg : (-1 : SL(2, ℤ)) ∈ Γ₄ := by
    change ((((-1 : SL(2, ℤ)).1 1 0 : ℤ) : ZMod 4) = 0)
    have hZ : (-1 : SL(2, ℤ)).1 1 0 = 0 := by
      simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Matrix.one_apply]
    rw [hZ, Int.cast_zero]
  have hZero : (∫ z in S, Q z) = 0 :=
    integral_compact_current_zero Γ₄ hNeg J (B := 2 * Y) (by linarith)
      (hJ Y hY) hSupp (cutoffFlux_slash Y hLaw hdF hRaise)
  have hQ : IntegrableOn Q S := integrableOn_weightedCurl Γ₄ J (hJ Y hY) hSupp
  have hQr : IntegrableOn (fun z : ℍ => (Q z).re) S := Complex.reCLM.integrable_comp hQ
  have hA : IntegrableOn A S := cutoffEnergy_integrableOn hY (continuous_profile hG)
  have hB : IntegrableOn B S := cutoffEnergy_integrableOn hY (continuous_profile hF)
  have hP : IntegrableOn P S := (normSquare_integrableOn_of_mass (continuous_profile hF) hMass).indicator hT
  have hR : IntegrableOn R S := (hQr.add hA).sub (hB.const_mul δ)
  have hW : IntegrableOn W S := (hA.add (hP.const_mul (C ^ 2))).div_const 2
  have hLe (z : ℍ) : R z ≤ W z := by
    have hPoint := congrArg Complex.re (weightedCurl_cutoffFlux_eq_shifted_energy hY hdF hdG hRaise hAdj z)
    change (Q z).re = (-(A z : ℂ) + (δ : ℂ) * (B z : ℂ) + weightedCutoffError Y F G z).re at hPoint
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hPoint
    have hRz : R z = (weightedCutoffError Y F G z).re := by unfold R; linarith
    rw [hRz]
    exact hBound Y hY N hNY F G z
  have hI := integral_mono hR hW hLe
  have hZeroRe : (∫ z in S, (Q z).re) = 0 := by
    have hRe : (∫ z in S, (Q z).re) = (∫ z in S, Q z).re := integral_re hQ
    rw [hRe, hZero, Complex.zero_re]
  have hRInt : (∫ z in S, R z) = (∫ z in S, A z) - δ * (∫ z in S, B z) := by
    unfold R
    rw [integral_sub (hQr.add hA) (hB.const_mul δ), integral_add hQr hA, hZeroRe, zero_add,
      integral_const_mul]
  have hWInt : (∫ z in S, W z) = ((∫ z in S, A z) + C ^ 2 * (∫ z in S, P z)) / 2 := by
    unfold W
    rw [integral_div, integral_add hA (hP.const_mul (C ^ 2)), integral_const_mul]
  have hPInt : (∫ z in S, P z) = ∫ z in S ∩ T, ‖F z‖ ^ 2 := by
    change (∫ z in S, T.indicator (fun u : ℍ => ‖F u‖ ^ 2) z) = _
    rw [integral_indicator hT, Measure.restrict_restrict hT, inter_comm T S]
  rw [hRInt, hWInt, hPInt] at hI
  linarith

end
end ManuscriptAudit.Paper8MaassGapEnergy

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassGapEnergy.odd_shifted_cutoff_energy_le_tail
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
