import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.L2Space
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassLevelFourTail
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassEnergyCompletion

/-! The covariant graph norm is the sum of the three actual squared L² components. -/

namespace ManuscriptAudit.Paper8OddMaassGraphNorm

open Filter MeasureTheory UpperHalfPlane
open Paper8OddMaassHilbertCore Paper8OddMaassCovariantGradient
open Paper8OddMaassEnergyCompletion Paper8OddMaassLevelFourTail
open Paper8OddGlobalCutoffEnergy Paper8OddMaassCuspTailEstimate
open Paper8OddCosetChartTransition FiniteIndexWeightZeroCosets
open scoped ENNReal NNReal MatrixGroups

noncomputable section

private theorem lintegral_sq_norm_eq_ofReal_toLp_sq {F : ℍ → ℂ} (hF : MemLp F 2 oddMaassMeasure) :
    (∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂oddMaassMeasure) =
      ENNReal.ofReal (‖hF.toLp F‖ ^ 2) := by
  let u := hF.toLp F
  let L := ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂oddMaassMeasure
  have hFi : Integrable (fun z => ‖F z‖ ^ 2) oddMaassMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hL : ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂oddMaassMeasure) = L :=
    ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall (fun z => sq_nonneg ‖F z‖))
  have hFin : L ≠ ⊤ := by rw [← hL]; exact ENNReal.ofReal_ne_top
  have hU :
      (∫⁻ z, (‖u z‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂oddMaassMeasure) = L := by
    apply lintegral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hF] with z hz
    change (‖u z‖₊ : ℝ≥0∞) ^ (2 : ℝ) = ENNReal.ofReal (‖F z‖ ^ 2)
    change u z = F z at hz
    rw [← hz, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow] <;> rfl
  have hNorm : ‖u‖ ^ 2 = L.toReal := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      L2.integral_inner_eq_sq_eLpNorm, hU, RCLike.ofReal_re]
  change L = ENNReal.ofReal (‖u‖ ^ 2)
  rw [hNorm, ENNReal.ofReal_toReal hFin]

theorem lintegral_coe_Lp_sq_norm_eq (F : OddMaassL2) :
    (∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂oddMaassMeasure) = ENNReal.ofReal (‖F‖ ^ 2) := by
  simpa only [Lp.toLp_coeFn] using lintegral_sq_norm_eq_ofReal_toLp_sq (Lp.memLp F)

theorem oddCoreEnergyGraph_norm_sq (f : OddSmoothCompactCore) :
    ‖oddCoreEnergyGraph f‖ ^ 2 =
      ‖oddCoreVector f‖ ^ 2 +
        (‖oddCovariantXL2 f‖ ^ 2 + ‖oddCovariantYL2 f‖ ^ 2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2] <;> rfl

theorem oddCoreGraphDensity_lintegral_eq_graphNorm (f : OddSmoothCompactCore) :
    (∫⁻ z in levelFourCells, ENNReal.ofReal (oddCoreGraphDensity f z)) =
      ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
  let DX (z : ℍ) := ENNReal.ofReal (‖oddCovariantDirection 1 (Complex.I / 4) f z‖ ^ 2)
  let DY (z : ℍ) := ENNReal.ofReal (‖oddCovariantDirection Complex.I 0 f z‖ ^ 2)
  let M (z : ℍ) := ENNReal.ofReal (‖(f : ℂ → ℂ) z‖ ^ 2)
  have hDX : Measurable DX := ENNReal.measurable_ofReal.comp
    ((oddCovariantDirection_continuous 1 (Complex.I / 4) f).norm.pow 2).measurable
  have hDY : Measurable DY := ENNReal.measurable_ofReal.comp
    ((oddCovariantDirection_continuous Complex.I 0 f).norm.pow 2).measurable
  have hG (z : ℍ) : ENNReal.ofReal (oddCoreGraphDensity f z) = (DX z + DY z) + M z := by
    rw [oddCoreGraphDensity_eq, ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hx : (∫⁻ z, DX z ∂oddMaassMeasure) = ENNReal.ofReal (‖oddCovariantXL2 f‖ ^ 2) :=
    lintegral_sq_norm_eq_ofReal_toLp_sq (oddCovariantDirection_memLp 1 (Complex.I / 4) f)
  have hy : (∫⁻ z, DY z ∂oddMaassMeasure) = ENNReal.ofReal (‖oddCovariantYL2 f‖ ^ 2) :=
    lintegral_sq_norm_eq_ofReal_toLp_sq (oddCovariantDirection_memLp Complex.I 0 f)
  have hm : (∫⁻ z, M z ∂oddMaassMeasure) = ENNReal.ofReal (‖oddCoreVector f‖ ^ 2) :=
    lintegral_sq_norm_eq_ofReal_toLp_sq (oddCore_memLp f)
  change (∫⁻ z, ENNReal.ofReal (oddCoreGraphDensity f z) ∂oddMaassMeasure) = _
  simp_rw [hG]
  rw [lintegral_add_left (hDX.add hDY), lintegral_add_left hDX, hx, hy, hm, oddCoreEnergyGraph_norm_sq,
    ENNReal.ofReal_add (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact add_comm _ _

theorem lintegral_levelFourCuspTail_le_graphNorm (f : OddSmoothCompactCore) {T : ℝ} (hT : 2 < T) :
    (∫⁻ z in levelFourCuspTail T, ENNReal.ofReal (‖(f : ℂ → ℂ) z‖ ^ 2)) ≤
      letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
      ENNReal.ofReal (oddCuspTailConstant / T ^ 2) * (Fintype.card levelFourRightCoset : ℝ≥0∞) *
        ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
  rw [← oddCoreGraphDensity_lintegral_eq_graphNorm]
  exact lintegral_levelFourCuspTail_le_graphDensity f hT

end
end ManuscriptAudit.Paper8OddMaassGraphNorm

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassGraphNorm.lintegral_levelFourCuspTail_le_graphNorm
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
