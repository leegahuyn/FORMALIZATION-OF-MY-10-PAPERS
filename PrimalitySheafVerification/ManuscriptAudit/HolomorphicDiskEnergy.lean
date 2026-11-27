import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.HolomorphicCircleEnergy

/-! The area mean inequality for a complex differentiable function on a closed disk. -/

namespace ManuscriptAudit.HolomorphicDiskEnergy

open Set Metric MeasureTheory
open scoped Topology Interval

private theorem polar_is_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

private theorem polar_disk_integral (F : ℂ → ℝ) (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, F z) =
      ∫ p : ℝ × ℝ in Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * F (circleMap 0 p.1 p.2) := by
  let S : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Iio R ×ˢ (univ : Set ℝ)
  have hS : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioo
  have hT : MeasurableSet T := measurableSet_Iio.prod MeasurableSet.univ
  have hST : T ∩ S = Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [T, S, mem_inter_iff, mem_prod, mem_Iio, mem_Ioi, mem_Ioo, mem_univ, and_true]
    tauto
  have h := Complex.integral_comp_polarCoord_symm ((ball (0 : ℂ) R).indicator F)
  change (∫ p : ℝ × ℝ in S, p.1 • (ball (0 : ℂ) R).indicator F (Complex.polarCoord.symm p)) = _ at h
  rw [integral_indicator measurableSet_ball] at h
  calc
    _ = (∫ p : ℝ × ℝ in S, p.1 • (ball (0 : ℂ) R).indicator F (Complex.polarCoord.symm p)) := h.symm
    _ = (∫ p : ℝ × ℝ in S, T.indicator (fun t => t.1 * F (circleMap 0 t.1 t.2)) p) := by
      refine setIntegral_congr_fun hS (fun p hp => ?_)
      have hp0 : 0 < p.1 := hp.1
      have hMem : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p ∈ T := by
        simp [T, mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp0]
      rcases p with ⟨r, θ⟩
      by_cases hIn : (r, θ) ∈ T
      · rw [indicator_of_mem hIn, indicator_of_mem (hMem.mpr hIn), polar_is_circleMap, smul_eq_mul]
      · rw [indicator_of_notMem hIn, indicator_of_notMem (hMem.not.mpr hIn), smul_zero]
    _ = _ := by
      rw [integral_indicator hT, Measure.restrict_restrict hT, hST]

private theorem circleAverage_eq_angle_integral (F : ℂ → ℝ) (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ)) =
      (2 * Real.pi) * Real.circleAverage F 0 r := by
  rw [Real.circleAverage_eq_integral_add (η := -Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ => F (circleMap 0 r θ)),
    zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]

theorem center_norm_sq_le_disk_energy {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R)) :
    (Real.pi * R ^ 2) * ‖f 0‖ ^ 2 ≤ ∫ z in ball (0 : ℂ) R, ‖f z‖ ^ 2 := by
  let F (z : ℂ) := ‖f z‖ ^ 2
  let G (p : ℝ × ℝ) := p.1 * F (circleMap 0 p.1 p.2)
  have hCompact : IsCompact (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hCont : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) := by
    refine continuous_fst.continuousOn.mul ?_
    refine (hf.continuousOn.norm.pow 2).comp (by
      change ContinuousOn (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) _
      unfold circleMap
      fun_prop) ?_
    intro p hp
    exact closedBall_subset_closedBall hp.1.2 (circleMap_mem_closedBall 0 hp.1.1 p.2)
  have hInt : IntegrableOn G (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
    exact (hCont.integrableOn_compact hCompact).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hVertical : IntegrableOn (fun r : ℝ => ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, G (r, θ))
      (Ioo 0 R) := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hInt
    exact hInt.integral_prod_left
  change _ ≤ ∫ z in ball (0 : ℂ) R, F z
  rw [polar_disk_integral]
  change _ ≤ ∫ p in Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi, G p ∂((volume : Measure ℝ).prod volume)
  rw [setIntegral_prod G hInt]
  have hLower (r : ℝ) (hr : r ∈ Ioo 0 R) :
      r * ((2 * Real.pi) * F 0) ≤ ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, G (r, θ) := by
    have hDiff := hf.diffContOnCl_ball (closedBall_subset_closedBall hr.2.le : closedBall (0 : ℂ) r ⊆ _)
    rw [← abs_of_pos hr.1] at hDiff
    have hAvg : F 0 ≤ Real.circleAverage F 0 r :=
      HolomorphicCircleEnergy.norm_sq_le_circleAverage hDiff
    simp only [G, integral_const_mul, circleAverage_eq_angle_integral]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAvg Real.two_pi_pos.le) hr.1.le
  have hConst : IntegrableOn (fun r : ℝ => r * ((2 * Real.pi) * F 0)) (Ioo 0 R) :=
    ((continuous_id.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hMono := setIntegral_mono_on hConst hVertical measurableSet_Ioo hLower
  calc
    _ = ∫ r : ℝ in Ioo 0 R, r * ((2 * Real.pi) * F 0) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
        intervalIntegral.integral_mul_const, integral_id]
      simp only [F]
      ring
    _ ≤ _ := hMono

theorem norm_sq_le_disk_energy {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) :
    (Real.pi * R ^ 2) * ‖f c‖ ^ 2 ≤ ∫ z in ball c R, ‖f z‖ ^ 2 := by
  let T (z : ℂ) := z + c
  have hClosed : MapsTo T (closedBall (0 : ℂ) R) (closedBall c R) := by
    intro z hz
    simpa only [T, mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using
      (mem_closedBall.mp hz)
  have hT : Differentiable ℂ T := by unfold T; fun_prop
  have hPre : T ⁻¹' ball c R = ball (0 : ℂ) R := by
    ext z
    simp [T, mem_ball, dist_eq_norm]
  have hShift := center_norm_sq_le_disk_energy hR (hf.comp hT.differentiableOn hClosed)
  have hMeasure : MeasurePreserving T (volume : Measure ℂ) volume :=
    measurePreserving_add_right volume c
  have hEmb : MeasurableEmbedding T :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hIntegral := hMeasure.setIntegral_preimage_emb hEmb (fun z : ℂ => ‖f z‖ ^ 2) (ball c R)
  rw [hPre] at hIntegral
  calc
    _ ≤ ∫ z in ball (0 : ℂ) R, ‖f (T z)‖ ^ 2 := by
      simpa only [Function.comp_apply, T, zero_add] using hShift
    _ = _ := hIntegral

end ManuscriptAudit.HolomorphicDiskEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HolomorphicDiskEnergy.center_norm_sq_le_disk_energy,
      ``ManuscriptAudit.HolomorphicDiskEnergy.norm_sq_le_disk_energy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
