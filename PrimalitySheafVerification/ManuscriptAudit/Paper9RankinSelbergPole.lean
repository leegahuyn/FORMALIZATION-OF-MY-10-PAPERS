import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import PrimalitySheafVerification.ManuscriptAudit.TentRegularity

/-!
# A real pole in the printed Rankin–Selberg denominator

Physical pp. 425–426, display (3.2), uses s(1-s)+t² in a
modulus-squared denominator for Re(s)>1. The real parameter
(1+sqrt 5)/2 has an interior pole at t=1. A positive numerator
weight near that point makes the actual t-integral nonintegrable.
The explicit compactly supported tent example addresses the inference
from compact support alone, without identifying the actual spectral
coefficients of Γ(2).
-/

namespace ManuscriptAudit.Paper9RankinSelbergPole

open MeasureTheory Set
open TentRegularity (tent)

noncomputable section

def parameter : ℝ := (1 + Real.sqrt 5) / 2

def denominator (s : ℂ) (t : ℝ) : ℂ := s * (1 - s) + (t : ℂ) ^ 2

theorem parameter_gt_one : 1 < parameter := by
  have h : 1 < Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  unfold parameter
  linarith

theorem parameter_product : parameter * (1 - parameter) = -1 := by
  unfold parameter
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

theorem denominator_at_parameter (t : ℝ) :
    denominator (parameter : ℂ) t = (((t ^ 2 - 1 : ℝ)) : ℂ) := by
  have h := congrArg (fun u : ℝ => (u : ℂ)) parameter_product
  unfold denominator
  push_cast at h ⊢
  rw [h]
  ring

theorem pole_in_positive_s_half_plane :
    ∃ s : ℂ, 1 < s.re ∧ denominator s 1 = 0 := by
  refine ⟨(parameter : ℂ), ?_, ?_⟩
  · simpa only [Complex.ofReal_re] using parameter_gt_one
  · norm_num [denominator_at_parameter]

def density (weight : ℝ → ℝ) (t : ℝ) : ℝ :=
  weight t / (t ^ 2 - 1) ^ 2

theorem not_integrableOn_of_positive_weight_near_pole (weight : ℝ → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hw : ∀ t ∈ Ioo (1 : ℝ) (1 + δ), a ≤ weight t) :
    ¬ IntegrableOn (density weight) (Ioo (1 : ℝ) (1 + δ)) := by
  intro h
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight 1
  have he : MeasurePreserving e volume volume := by
    simpa only [e, MeasurableEquiv.coe_addRight] using
      measurePreserving_add_right (volume : Measure ℝ) 1
  have hpre : e ⁻¹' Ioo (1 : ℝ) (1 + δ) = Ioo 0 δ := by
    ext x
    simp only [mem_preimage, e, MeasurableEquiv.coe_addRight, mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
  have hshift := (he.integrableOn_comp_preimage e.measurableEmbedding).2 h
  rw [hpre] at hshift
  change Integrable (fun x : ℝ => density weight (x + 1)) (volume.restrict (Ioo 0 δ)) at hshift
  have hMeas : Measurable (fun x : ℝ => (a / 9) * x ^ (-2 : ℝ)) := by fun_prop
  have hCmp : Integrable (fun x : ℝ => (a / 9) * x ^ (-2 : ℝ))
      (volume.restrict (Ioo 0 δ)) := by
    apply hshift.mono' hMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hx₀ : 0 < x := hx.1
    have hx₁ : x < δ := hx.2
    have hx₂ : x + 2 ≤ 3 := by linarith
    have hDen : ((x + 1) ^ 2 - 1) ^ 2 = x ^ 2 * (x + 2) ^ 2 := by ring
    have hPos : 0 < x ^ 2 * (x + 2) ^ 2 := by positivity
    have hLe : x ^ 2 * (x + 2) ^ 2 ≤ 9 * x ^ 2 := by
      have hs : (x + 2) ^ 2 ≤ (3 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx₂ 2
      nlinarith only [mul_le_mul_of_nonneg_left hs (sq_nonneg x)]
    have hW : a ≤ weight (x + 1) := hw _ ⟨by linarith, by linarith⟩
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hx₀.le, Real.rpow_two,
      density, hDen]
    calc
      _ = a / (9 * x ^ 2) := by field_simp [hx₀.ne'] <;> ring
      _ ≤ a / (x ^ 2 * (x + 2) ^ 2) :=
        div_le_div_of_nonneg_left ha.le hPos hLe
      _ ≤ _ := div_le_div_of_nonneg_right hW hPos.le
  have hNonzero : (a / 9 : ℝ) ≠ 0 := by positivity
  have hPow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioo 0 δ) := by
    apply (integrable_fun_smul_iff hNonzero (fun x : ℝ => x ^ (-2 : ℝ))).1
    simpa only [smul_eq_mul] using hCmp
  have hImpossible := (integrableOn_Ioo_rpow_iff hδ).1 hPow
  norm_num at hImpossible

def compactNumerator (t : ℝ) : ℂ := (Real.sqrt (tent 2 t) : ℝ)

theorem compactNumerator_zero_outside {t : ℝ} (ht : 2 ≤ |t|) : compactNumerator t = 0 := by
  simp only [compactNumerator, tent, max_eq_left (sub_nonpos.mpr ht), Real.sqrt_zero,
    Complex.ofReal_zero]

theorem norm_square_eq_density (t : ℝ) :
    ‖compactNumerator t / denominator (parameter : ℂ) t‖ ^ 2 = density (tent 2) t := by
  have h : 0 ≤ tent 2 t := le_max_left _ _
  rw [compactNumerator, denominator_at_parameter, norm_div, div_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs, Real.sq_sqrt h, sq_abs, density]

theorem compact_numerator_does_not_regularize :
    ¬ IntegrableOn (fun t : ℝ => ‖compactNumerator t / denominator (parameter : ℂ) t‖ ^ 2)
      (Ioo (1 : ℝ) (1 + 1 / 2)) := by
  simp_rw [norm_square_eq_density]
  apply not_integrableOn_of_positive_weight_near_pole (tent 2) (a := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  intro t ht
  have ht₀ : 0 < t := zero_lt_one.trans ht.1
  have ht₁ := ht.2
  unfold tent
  rw [abs_of_pos ht₀]
  exact (by linarith : (1 / 2 : ℝ) ≤ 2 - t).trans (le_max_right _ _)

end
end ManuscriptAudit.Paper9RankinSelbergPole

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9RankinSelbergPole.pole_in_positive_s_half_plane,
      ``ManuscriptAudit.Paper9RankinSelbergPole.not_integrableOn_of_positive_weight_near_pole,
      ``ManuscriptAudit.Paper9RankinSelbergPole.compactNumerator_zero_outside,
      ``ManuscriptAudit.Paper9RankinSelbergPole.norm_square_eq_density,
      ``ManuscriptAudit.Paper9RankinSelbergPole.compact_numerator_does_not_regularize] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
