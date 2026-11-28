import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8GlobalWeightTwoGreen

/-! The explicit standard-domain Green regularity conditions follow from ordinary C¹ smoothness. -/

namespace ManuscriptAudit.Paper8StandardGreenRegularity

open Function MeasureTheory Set UpperHalfPlane MaassLaplacian
open Paper8GlobalWeightTwoGreen Paper8StandardDomainCurrentGreen Paper8StandardDomainSidePairing
open Paper8CurvedGreenChart Paper8MaassCurlCalculus RectangularIntegral

theorem traceRegularity_of_contDiffOn (f : ℍ → ℂ) {B : ℝ} (hB : 1 ≤ B)
    (hF : ContDiffOn ℝ 1 (asComplexCurrent f) {w : ℂ | 0 < w.im}) :
    TraceRegularity f B := by
  let S : Set ℂ := {w : ℂ | 0 < w.im}
  let X : Set ℝ := Icc (-(1 / 2)) (1 / 2)
  let R := rectangle (-(1 / 2)) (1 / 2) 0 1
  let J := asComplexCurrent f
  let P (p : ℝ × ℝ) := point arcHeight B p.1 p.2
  have hOpen : IsOpen S := isOpen_lt continuous_const Complex.continuous_im
  have hA : Continuous arcHeight := by
    unfold arcHeight
    exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  have hA' : ContinuousOn (deriv arcHeight) X := by
    have h := continuous_id.neg.continuousOn.div hA.continuousOn
      (fun x (hx : x ∈ X) => (arcHeight_pos (abs_le.mpr hx)).ne')
    exact h.congr (fun x hx => (arcHeight_hasDerivAt (abs_le.mpr hx)).deriv)
  have hD (v : ℂ) : ContinuousOn (fun w : ℂ => fderiv ℝ J w v) S := by
    let L (w : ℂ) := (w, v)
    have hL : Continuous L := continuous_id.prodMk continuous_const
    have hm : MapsTo L S (S ×ˢ (univ : Set ℂ)) := fun _ hw => ⟨hw, mem_univ _⟩
    have hc := (hF.continuousOn_fderivWithin_apply hOpen.uniqueDiffOn (le_refl 1)).comp
      hL.continuousOn hm
    refine hc.congr ?_
    intro w hw
    change fderiv ℝ J w v = fderivWithin ℝ J S w v
    rw [fderivWithin_of_isOpen hOpen hw]
  have hCurl : ContinuousOn (complexCurl J) S := by
    unfold complexCurl
    exact (continuousOn_const.mul (hD 1)).sub (hD Complex.I)
  have hMap : MapsTo P R S := by
    intro p hp
    have hHalf : |p.1| ≤ 1 / 2 := abs_le.mpr hp.1
    have hArc1 : arcHeight p.1 ≤ 1 := by
      unfold arcHeight
      exact Real.sqrt_le_one.2 (by nlinarith [sq_nonneg p.1])
    change 0 < (complexPoint p.1 (height arcHeight B p.1 p.2)).im
    rw [complexPoint_im, height]
    exact add_pos_of_pos_of_nonneg (arcHeight_pos hHalf)
      (mul_nonneg hp.2.1 (sub_nonneg.mpr (hArc1.trans hB)))
  have hP : Continuous P := by
    unfold P point height complexPoint
    fun_prop
  have hJ := hF.continuousOn.comp hP.continuousOn hMap
  have hD1 := (hD 1).comp hP.continuousOn hMap
  have hDI := (hD Complex.I).comp hP.continuousOn hMap
  have hDX : ContinuousOn (fun p : ℝ × ℝ => deriv arcHeight p.1) R :=
    hA'.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hDXC : ContinuousOn (fun p : ℝ × ℝ => ((deriv arcHeight p.1 : ℝ) : ℂ)) R :=
    Complex.continuous_ofReal.comp_continuousOn hDX
  have hSpan : ContinuousOn (fun p : ℝ × ℝ => ((B - arcHeight p.1 : ℝ) : ℂ)) R :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.sub (hA.comp continuous_fst)).continuousOn)
  have hSlope : ContinuousOn (fun p : ℝ × ℝ => (Paper8CurvedGreenChart.slope arcHeight p.1 p.2 : ℂ)) R :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.sub continuous_snd).continuousOn.mul hDX)
  refine ⟨hCurl.mono ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.im_pos
  · intro x hx t ht
    have h := hMap (show (x,t) ∈ R from ⟨hx, ht⟩)
    exact ((hF _ h).contDiffAt (hOpen.mem_nhds h)).differentiableAt (by norm_num)
  · unfold rateX
    exact ((continuousOn_const.mul hDXC).mul hJ).add
      ((continuousOn_const.mul hSpan).mul (hD1.add (hSlope.mul hDI)))
  · unfold rateT
    exact ((continuousOn_const.mul hDXC).mul hJ).add
      ((continuousOn_const.add (continuousOn_const.mul hSlope)).mul (hSpan.mul hDI))

end ManuscriptAudit.Paper8StandardGreenRegularity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8StandardGreenRegularity.traceRegularity_of_contDiffOn
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
