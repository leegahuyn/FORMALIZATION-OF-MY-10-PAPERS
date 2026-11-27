import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HolomorphicDiskEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Local area and horizontal-period comparisons for weighted holomorphic cusp energy. -/

namespace ManuscriptAudit.HolomorphicStripEnergy

open Set Filter Metric MeasureTheory
open scoped Topology Interval

noncomputable section

def horizontalEnergy (H : ℂ → ℂ) (width y : ℝ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..width, ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2

def weightedEnergy (H : ℂ → ℂ) (width y : ℝ) : ℝ :=
  horizontalEnergy H width y / y ^ (3 / 2 : ℝ)

private theorem horizontal_closedBound (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {w y a b : ℝ} (hy : 0 < y)
    (hab : a ≤ b) (hw : b ≤ a + w)
    (hPer : Function.Periodic (fun x : ℝ => ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) w) :
    (∫ x : ℝ in Ioo a b, ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤ horizontalEnergy H w y := by
  let f (x : ℝ) := ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2
  have hC : Continuous f := by
    let L (x : ℝ) := (x : ℂ) + (y : ℂ) * Complex.I
    have hL : Continuous L := by unfold L; fun_prop
    have hHL : Continuous (H ∘ L) :=
      hH.continuousOn.comp_continuous hL (fun x => by
        simp [L, Complex.mul_im, hy])
    exact hHL.norm.pow 2
  change (∫ x in Ioo a b, f x) ≤ horizontalEnergy H w y
  calc
    _ = ∫ x in a..b, f x := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ x in a..a + w, f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hw
        (Eventually.of_forall (fun x => sq_nonneg _)) (hC.intervalIntegrable _ _)
    _ = _ := by simpa only [horizontalEnergy, zero_add] using hPer.intervalIntegral_add_eq a 0

private theorem coord_eq (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.measurableEquivRealProd_symm_apply, Complex.mul_re]
  · simp [Complex.measurableEquivRealProd_symm_apply, Complex.mul_im]

theorem disk_energy_le_rectangle (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (z : ℂ) {r : ℝ}
    (hY : 0 < z.im - r) :
    ∃ E : ℝ → ℝ,
      IntegrableOn E (Ioo (z.im - r) (z.im + r)) ∧
      (∫ u in ball z r, ‖H u‖ ^ 2) ≤ ∫ y in Ioo (z.im - r) (z.im + r), E y ∧
      ∀ y, E y = ∫ x : ℝ in Ioo (z.re - r) (z.re + r),
        ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
  let X := Ioo (z.re - r) (z.re + r)
  let Y := Ioo (z.im - r) (z.im + r)
  let G (p : ℝ × ℝ) := ‖H (Complex.measurableEquivRealProd.symm p)‖ ^ 2
  have hC : Continuous (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p) :=
    Complex.equivRealProdCLM.symm.continuous
  have hInt : IntegrableOn G (X ×ˢ Y) ((volume : Measure ℝ).prod volume) := by
    let K := Icc (z.re - r) (z.re + r) ×ˢ Icc (z.im - r) (z.im + r)
    have hHK : ContinuousOn G K := by
      apply ContinuousOn.pow
      apply ContinuousOn.norm
      refine hH.continuousOn.comp hC.continuousOn (fun p hp => ?_)
      change 0 < (Complex.measurableEquivRealProd.symm p).im
      simpa only [Complex.measurableEquivRealProd_symm_apply] using hY.trans_le hp.2.1
    exact (hHK.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hSub : Complex.measurableEquivRealProd.symm ⁻¹' ball z r ⊆ X ×ˢ Y := by
    intro p hp
    have hD : ‖Complex.measurableEquivRealProd.symm p - z‖ < r := mem_ball_iff_norm.mp hp
    have hRe : |p.1 - z.re| < r := by
      simpa only [Complex.sub_re, Complex.measurableEquivRealProd_symm_apply] using
        (Complex.abs_re_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans_lt hD
    have hIm : |p.2 - z.im| < r := by
      simpa only [Complex.sub_im, Complex.measurableEquivRealProd_symm_apply] using
        (Complex.abs_im_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans_lt hD
    have hpX := abs_lt.mp hRe
    have hpY := abs_lt.mp hIm
    exact ⟨⟨by linarith [hpX.1], by linarith [hpX.2]⟩,
      ⟨by linarith [hpY.1], by linarith [hpY.2]⟩⟩
  let E (y : ℝ) := ∫ x : ℝ in X, G (x, y)
  have hDisk :
      (∫ p in Complex.measurableEquivRealProd.symm ⁻¹' ball z r, G p) =
        ∫ u in ball z r, ‖H u‖ ^ 2 :=
    Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding (fun u : ℂ => ‖H u‖ ^ 2) _
  have hRect : (∫ p in X ×ˢ Y, G p) = ∫ y in Y, E y := by
    unfold IntegrableOn at hInt
    change (∫ p, G p ∂((volume : Measure ℝ).prod volume).restrict (X ×ˢ Y)) =
      ∫ y in Y, E y
    rw [← Measure.prod_restrict] at hInt ⊢
    exact integral_prod_symm G hInt
  refine ⟨E, ?_, ?_, fun y => by simp only [E, G, X, coord_eq]⟩
  · rw [IntegrableOn, ← Measure.prod_restrict] at hInt
    exact hInt.integral_prod_right
  · rw [← hDisk, ← hRect]
    exact setIntegral_mono_set hInt (Eventually.of_forall (fun p => sq_nonneg _))
      hSub.eventuallyLE

theorem disk_energy_le_weighted_cusp_energy (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {w : ℝ} (hw : 0 < w)
    (hPer : ∀ y : ℝ, 0 < y →
      Function.Periodic (fun x : ℝ => ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) w)
    (hLTwo : IntegrableOn (weightedEnergy H w) (Ioi 1))
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hWidth : 2 * r ≤ w) (hY : 1 ≤ z.im - r) :
    (∫ u in ball z r, ‖H u‖ ^ 2) ≤ (z.im + r) ^ 2 * ∫ y in Ioi (1 : ℝ), weightedEnergy H w y := by
  let Y := Ioo (z.im - r) (z.im + r)
  have hSub : Y ⊆ Ioi (1 : ℝ) := fun _ ht => hY.trans_lt ht.1
  have hNonneg (y : ℝ) (hy : y ∈ Ioi (1 : ℝ)) : 0 ≤ weightedEnergy H w y := by
    unfold weightedEnergy horizontalEnergy
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hw.le (fun x => sq_nonneg _))
      (Real.rpow_nonneg (zero_le_one.trans hy.le) _)
  obtain ⟨E, hE, hDisk, hEeq⟩ := disk_energy_le_rectangle H hH z (zero_lt_one.trans_le hY)
  have hCompare (t : ℝ) (ht : t ∈ Y) : E t ≤ (z.im + r) ^ 2 * weightedEnergy H w t := by
    have ht1 : 1 < t := hSub ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hRp : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hRpow : t ^ (3 / 2 : ℝ) ≤ (z.im + r) ^ 2 := by
      calc
        _ ≤ t ^ 2 := by
          rw [← Real.rpow_two]
          exact Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num)
        _ ≤ _ := pow_le_pow_left₀ ht0.le ht.2.le 2
    rw [hEeq t]
    calc
      _ ≤ horizontalEnergy H w t :=
        horizontal_closedBound H hH ht0 (by linarith) (by linarith) (hPer t ht0)
      _ = t ^ (3 / 2 : ℝ) * weightedEnergy H w t := by
        unfold weightedEnergy
        field_simp [hRp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hRpow (hNonneg t ht1)
  have hIntegrable := (hLTwo.mono_set hSub).const_mul ((z.im + r) ^ 2)
  have hRectCompare := setIntegral_mono_on hE hIntegrable measurableSet_Ioo hCompare
  have hEv : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] weightedEnergy H w :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hNonneg)
  calc
    _ ≤ ∫ y in Y, E y := hDisk
    _ ≤ ∫ y in Y, (z.im + r) ^ 2 * weightedEnergy H w y := hRectCompare
    _ = (z.im + r) ^ 2 * ∫ y in Y, weightedEnergy H w y := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hLTwo hEv hSub.eventuallyLE) (sq_nonneg _)

end
end ManuscriptAudit.HolomorphicStripEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HolomorphicStripEnergy.disk_energy_le_rectangle,
      ``ManuscriptAudit.HolomorphicStripEnergy.disk_energy_le_weighted_cusp_energy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
