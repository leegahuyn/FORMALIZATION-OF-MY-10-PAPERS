import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The native L² classes of width-two horizontal cusp profiles carry
the exact measured distance, and continuous representatives determine
their upper boundary value. -/

namespace ManuscriptAudit.Paper10CuspProfileHilbert

open MeasureTheory Set
open scoped Interval Topology RealInnerProductSpace

noncomputable section

abbrev collarMeasure : Measure ℝ := volume.restrict (Ioc 4 6)
abbrev ProfileL2 := Lp ℝ 2 collarMeasure

theorem memLp (f : ℝ → ℝ) (hf : Continuous f) : MemLp f 2 collarMeasure :=
  (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).mpr
    ((hf.pow 2).intervalIntegrable (μ := volume) 4 6).1

def vector (f : ℝ → ℝ) (hf : Continuous f) : ProfileL2 :=
  (memLp f hf).toLp f

theorem distance_squared (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    ‖vector f hf - vector g hg‖^2 = ∫ y : ℝ in 4..6, (f y - g y)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    intervalIntegral.integral_of_le (by norm_num : (4:ℝ) ≤ 6)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (vector f hf) (vector g hg),
    (memLp f hf).coeFn_toLp, (memLp g hg).coeFn_toLp] with y h hF hG
  rw [h, Pi.sub_apply, hF, hG, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Continuous representatives of the same actual measured class have
the same trace at height six. -/
theorem trace_eq (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h : vector f hf = vector g hg) : f 6 = g 6 := by
  let F : ℝ → ℝ := fun y ↦ (f y - g y)^2
  have hF : Continuous F := (hf.sub hg).pow 2
  have hz : (∫ y : ℝ in 4..6, F y) = 0 := by
    have hNorm := distance_squared f g hf hg
    rw [h, sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hNorm
    exact hNorm.symm
  by_contra hNe
  have hPos : 0 < F 6 := sq_pos_of_ne_zero (sub_ne_zero.mpr hNe)
  have hN : {y : ℝ | 0 < F y} ∈ 𝓝 (6:ℝ) :=
    (isOpen_lt continuous_const hF).mem_nhds hPos
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hN
  let a : ℝ := max 4 (6-r/2)
  have haLow : 4 ≤ a := le_max_left _ _
  have haHigh : a < 6 := max_lt_iff.mpr ⟨by norm_num, by linarith⟩
  have hTail : 0 < ∫ y : ℝ in a..6, F y := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hF.intervalIntegrable (μ := volume) a 6) _ haHigh
    intro y hy
    have hyL : 6-r/2 < y := (le_max_right _ _).trans_lt hy.1
    have hyR : y < 6 := hy.2
    apply hBall
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hyR)]
    linarith
  have hHead : 0 ≤ ∫ y : ℝ in 4..a, F y :=
    intervalIntegral.integral_nonneg haLow (fun y _ ↦ sq_nonneg (f y - g y))
  have hSum := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) 4 a) (hF.intervalIntegrable (μ := volume) a 6)
  linarith

end
end ManuscriptAudit.Paper10CuspProfileHilbert

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CuspProfileHilbert.distance_squared,
      ``ManuscriptAudit.Paper10CuspProfileHilbert.trace_eq] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
