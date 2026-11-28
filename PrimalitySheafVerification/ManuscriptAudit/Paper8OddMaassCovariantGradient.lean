import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassHilbertCore

/-! The actual weight −1/2 covariant directional components on the smooth L² core. -/

namespace ManuscriptAudit.Paper8OddMaassCovariantGradient

open Filter MeasureTheory Set UpperHalfPlane
open Paper8OddMaassHilbertCore Paper8OddGlobalCutoffEnergy Paper8CompactCurrentGreen
open Paper8ModularHeightCutoff Paper8ActualEtaSquaredModularity Paper8MaassWirtinger
open scoped MatrixGroups ContDiff ENNReal Topology

noncomputable section

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem oddCore_differentiableAt (f : OddSmoothCompactCore) (z : ℍ) :
    DifferentiableAt ℝ (f : ℂ → ℂ) z :=
  ((f.2.2.1 z z.im_pos).contDiffAt (isOpen_upper.mem_nhds z.im_pos)).differentiableAt (by norm_num)

theorem oddCore_directional_derivative_continuous (f : OddSmoothCompactCore) (v : ℂ) :
    Continuous (fun z : ℍ => fderiv ℝ (f : ℂ → ℂ) (z : ℂ) v) := by
  let S : Set ℂ := {w : ℂ | 0 < w.im}
  let F : ℂ → ℂ := f
  let L (w : ℂ) := (w, v)
  have hL : Continuous L := continuous_id.prodMk continuous_const
  have hm : MapsTo L S (S ×ˢ (univ : Set ℂ)) := fun _ hw => ⟨hw, mem_univ _⟩
  have hC : ContDiffOn ℝ 1 F S := f.2.2.1.of_le (by norm_num)
  have h := (hC.continuousOn_fderivWithin_apply isOpen_upper.uniqueDiffOn (le_refl 1)).comp
    hL.continuousOn hm
  have hOut : ContinuousOn (fun w : ℂ => fderiv ℝ F w v) S := by
    refine h.congr fun w hw => ?_
    change fderiv ℝ F w v = fderivWithin ℝ F S w v
    rw [fderivWithin_of_isOpen isOpen_upper hw]
  exact hOut.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

private theorem fderiv_eq_zero_of_above {F : ℂ → ℂ} {B : ℝ}
    (hSupport : ∀ z : ℍ, B < maximumHeight z → F z = 0)
    (z : ℍ) (hz : B < maximumHeight z) : fderiv ℝ F (z : ℂ) = 0 := by
  let g := Classical.choose (ModularGroup.exists_max_im z)
  have hg : B < (g • z).im := hz
  have hComplex : B < (fractionalLinear g z).im := by
    rw [fractionalLinear_eq, UpperHalfPlane.coe_im]
    exact hg
  have hAction : ContinuousAt (fun w : ℂ => (fractionalLinear g w).im) z :=
    Complex.continuous_im.continuousAt.comp ((fractionalLinear_hasDerivAt g z).continuousAt)
  have hLocal : F =ᶠ[𝓝 (z : ℂ)] (Function.const ℂ (0 : ℂ)) := by
    filter_upwards [isOpen_upper.mem_nhds z.im_pos,
      hAction.tendsto.eventually (Ioi_mem_nhds hComplex)] with w hw hW
    let u : ℍ := ⟨w, hw⟩
    apply hSupport u
    have hV : B < (g • u).im := by
      change B < (fractionalLinear g u).im at hW
      rw [fractionalLinear_eq, UpperHalfPlane.coe_im] at hW
      exact hW
    exact hV.trans_le (im_smul_le_maximumHeight u g)
  rw [hLocal.fderiv_eq (𝕜 := ℝ), fderiv_const]

def oddCovariantDirection (v c : ℂ) (f : OddSmoothCompactCore) (z : ℍ) : ℂ :=
  (z.im : ℂ) * fderiv ℝ (f : ℂ → ℂ) (z : ℂ) v + c * (f : ℂ → ℂ) z

theorem oddCovariantDirection_continuous (v c : ℂ) (f : OddSmoothCompactCore) :
    Continuous (oddCovariantDirection v c f) := by
  unfold oddCovariantDirection
  exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (oddCore_directional_derivative_continuous f v)).add (continuous_const.mul (oddCore_continuous f))

theorem oddCovariantDirection_memLp (v c : ℂ) (f : OddSmoothCompactCore) :
    MemLp (oddCovariantDirection v c f) 2 oddMaassMeasure := by
  obtain ⟨B, hB⟩ := f.2.2.2
  have hC := oddCovariantDirection_continuous v c f
  apply (memLp_two_iff_integrable_sq_norm hC.measurable.aestronglyMeasurable).2
  change IntegrableOn (fun z : ℍ => ‖oddCovariantDirection v c f z‖ ^ 2) levelFourCells
  exact integrableOn_cusp_support (CongruenceSubgroup.Gamma0 4) _
    (hC.norm.pow 2) (B := B) (fun z hz => by
      unfold oddCovariantDirection
      rw [fderiv_eq_zero_of_above hB z hz, hB z hz]
      simp)

theorem oddCovariantDirection_add (v c : ℂ) (f g : OddSmoothCompactCore) :
    oddCovariantDirection v c (f + g) = oddCovariantDirection v c f + oddCovariantDirection v c g := by
  funext z
  change (z.im : ℂ) * fderiv ℝ ((f : ℂ → ℂ) + (g : ℂ → ℂ)) (z : ℂ) v +
      c * ((f : ℂ → ℂ) z + (g : ℂ → ℂ) z) =
    oddCovariantDirection v c f z + oddCovariantDirection v c g z
  rw [fderiv_add (oddCore_differentiableAt f z) (oddCore_differentiableAt g z)]
  simp only [ContinuousLinearMap.add_apply, oddCovariantDirection]
  ring

theorem oddCovariantDirection_smul (v c a : ℂ) (f : OddSmoothCompactCore) :
    oddCovariantDirection v c (a • f) = a • oddCovariantDirection v c f := by
  funext z
  change (z.im : ℂ) * fderiv ℝ (fun w => a * (f : ℂ → ℂ) w) (z : ℂ) v +
      c * (a * (f : ℂ → ℂ) z) = a * oddCovariantDirection v c f z
  rw [fderiv_const_mul (oddCore_differentiableAt f z)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, oddCovariantDirection]
  ring

def oddCovariantDirectionL2 (v c : ℂ) : OddSmoothCompactCore →ₗ[ℂ] OddMaassL2 where
  toFun f := (oddCovariantDirection_memLp v c f).toLp (oddCovariantDirection v c f)
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (oddCovariantDirection_memLp v c (f + g)),
      MemLp.coeFn_toLp (oddCovariantDirection_memLp v c f),
      MemLp.coeFn_toLp (oddCovariantDirection_memLp v c g),
      Lp.coeFn_add ((oddCovariantDirection_memLp v c f).toLp _) ((oddCovariantDirection_memLp v c g).toLp _)]
      with z h₁ h₂ h₃ h₄
    rw [h₁, h₄]
    change oddCovariantDirection v c (f + g) z =
      ((oddCovariantDirection_memLp v c f).toLp _) z + ((oddCovariantDirection_memLp v c g).toLp _) z
    rw [oddCovariantDirection_add, h₂, h₃] <;> rfl
  map_smul' := by
    intro a f
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (oddCovariantDirection_memLp v c (a • f)),
      MemLp.coeFn_toLp (oddCovariantDirection_memLp v c f),
      Lp.coeFn_smul a ((oddCovariantDirection_memLp v c f).toLp _)]
      with z h₁ h₂ h₃
    rw [h₁, h₃]
    change oddCovariantDirection v c (a • f) z = a • ((oddCovariantDirection_memLp v c f).toLp _) z
    rw [oddCovariantDirection_smul, h₂] <;> rfl

abbrev oddCovariantXL2 := oddCovariantDirectionL2 1 (Complex.I / 4)
abbrev oddCovariantYL2 := oddCovariantDirectionL2 Complex.I 0

end
end ManuscriptAudit.Paper8OddMaassCovariantGradient

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCovariantGradient.oddCovariantDirectionL2
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
