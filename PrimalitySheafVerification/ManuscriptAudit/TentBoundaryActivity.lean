import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tent mass for coefficients concentrated near a support endpoint

On physical PDF p. 427, Proposition 6 uses the unweighted window activity
in Lemma 3.8 to infer a uniform positive weighted mass. At T=1 and with
Lebesgue measure on the spectral variable, normalized coefficients supported
in a layer of width δ have unweighted squared integral 1 and weighted
integral δ/2. This tests the implication from the window bound alone. The
coefficients here are L² test functions and are separate from the manuscript's
Eisenstein coefficients and its spectral measure.
-/

namespace ManuscriptAudit.TentBoundaryActivity

open MeasureTheory Filter Set
open scoped Topology

def rightLayer (δ : ℝ) : Set ℝ := Ioc (1 - δ) 1

noncomputable def endpointCoeff (δ : ℝ) : ℝ → ℝ :=
  (rightLayer δ).indicator (fun _ => Real.sqrt δ⁻¹)

noncomputable def unitTent (t : ℝ) : ℝ := max 0 (1 - |t|)

noncomputable def weightedMass (f : ℝ → ℝ) : ℝ :=
  ∫ t, unitTent t * ‖f t‖ ^ 2

private theorem measurableSet_rightLayer (δ : ℝ) : MeasurableSet (rightLayer δ) :=
  measurableSet_Ioc

private theorem sq_norm_endpointCoeff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ‖endpointCoeff δ t‖ ^ 2 = (rightLayer δ).indicator (fun _ => δ⁻¹) t := by
  by_cases ht : t ∈ rightLayer δ
  · simp only [endpointCoeff, Set.indicator_of_mem ht, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (inv_nonneg.mpr hδ.le)]
  · simp [endpointCoeff, ht]

private theorem rightLayer_subset (δ : ℝ) (hδ : δ ≤ 1) :
    rightLayer δ ⊆ Icc (-1 : ℝ) 1 := by
  intro t ht
  have hi : 1 - δ < t ∧ t ≤ 1 := Set.mem_Ioc.mp ht
  exact ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans
    ((sub_nonneg.mpr hδ).trans hi.1.le), hi.2⟩

theorem endpointCoeff_support {δ : ℝ} (hδ : δ ≤ 1) :
    Function.support (endpointCoeff δ) ⊆ Icc (-1 : ℝ) 1 := by
  intro t ht
  apply rightLayer_subset δ hδ
  by_contra hn
  exact (Function.mem_support.mp ht) (by simp [endpointCoeff, hn])

/-- These are genuine L² coefficients with unweighted activity one on [-1,1]. -/
theorem endpointCoeff_unit_activity {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun t => ‖endpointCoeff δ t‖ ^ 2) ∧
      (∫ t in Icc (-1 : ℝ) 1, ‖endpointCoeff δ t‖ ^ 2) = 1 := by
  constructor
  · simp_rw [sq_norm_endpointCoeff hδ]
    apply (integrable_indicator_iff (measurableSet_rightLayer δ)).2
    exact integrableOn_const (by simp [rightLayer, Real.volume_Ioc])
  · simp_rw [sq_norm_endpointCoeff hδ]
    rw [setIntegral_indicator (measurableSet_rightLayer δ),
      inter_eq_right.mpr (rightLayer_subset δ hδ1)]
    change (∫ t in Ioc (1 - δ) 1, (δ⁻¹ : ℝ)) = 1
    rw [← intervalIntegral.integral_of_le (sub_le_self _ hδ.le),
      intervalIntegral.integral_const, smul_eq_mul]
    rw [show 1 - (1 - δ) = δ by ring, mul_inv_cancel₀ hδ.ne']

/-- The normalized coefficient has weighted mass exactly half its layer width. -/
theorem endpointCoeff_weighted_mass {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    weightedMass (endpointCoeff δ) = δ / 2 := by
  have hterm (t : ℝ) :
      unitTent t * ‖endpointCoeff δ t‖ ^ 2 =
        (rightLayer δ).indicator (fun x => (1 - x) * δ⁻¹) t := by
    by_cases ht : t ∈ rightLayer δ
    · have hi : 1 - δ < t ∧ t ≤ 1 := Set.mem_Ioc.mp ht
      have hpos : 0 ≤ t := (sub_nonneg.mpr hδ1).trans hi.1.le
      have hleft : 0 ≤ 1 - t := sub_nonneg.mpr hi.2
      simp only [sq_norm_endpointCoeff hδ, Set.indicator_of_mem ht, unitTent,
        abs_of_nonneg hpos, max_eq_right hleft]
    · simp only [sq_norm_endpointCoeff hδ, Set.indicator_of_notMem ht, mul_zero]
  have hIntegral : (∫ t : ℝ in (1 - δ)..1, 1 - t) = δ ^ 2 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t) 1]
    rw [sub_self, show 1 - (1 - δ) = δ by ring, integral_id] <;> ring
  unfold weightedMass
  simp_rw [hterm]
  rw [integral_indicator (measurableSet_rightLayer δ)]
  change (∫ t in Ioc (1 - δ) 1, (1 - t) * δ⁻¹) = δ / 2
  rw [← intervalIntegral.integral_of_le (sub_le_self _ hδ.le),
    intervalIntegral.integral_mul_const, hIntegral]
  calc
    _ = (δ * δ⁻¹) * (δ / 2) := by ring
    _ = δ / 2 := by rw [mul_inv_cancel₀ hδ.ne', one_mul]

noncomputable def width (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

private theorem width_pos (m : ℕ) : 0 < width m := by
  unfold width
  positivity

private theorem width_le_one (m : ℕ) : width m ≤ 1 := by
  unfold width
  apply (div_le_iff₀ (show 0 < (m : ℝ) + 1 by positivity)).2
  rw [one_mul]
  exact le_add_of_nonneg_left (Nat.cast_nonneg m)

theorem unit_activity_for_all (m : ℕ) :
    Integrable (fun t => ‖endpointCoeff (width m) t‖ ^ 2) ∧
      (∫ t in Icc (-1 : ℝ) 1, ‖endpointCoeff (width m) t‖ ^ 2) = 1 :=
  endpointCoeff_unit_activity (width_pos m) (width_le_one m)

theorem weighted_mass_tendsto_zero :
    Tendsto (fun m : ℕ => weightedMass (endpointCoeff (width m))) atTop (𝓝 0) := by
  have heq : (fun m : ℕ => weightedMass (endpointCoeff (width m))) =
      (fun m : ℕ => width m / 2) := by
    funext m
    exact endpointCoeff_weighted_mass (width_pos m) (width_le_one m)
  rw [heq]
  have hw : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [zero_div] using hw.div_const (2 : ℝ)

/-- No strictly positive eventual lower bound follows from the unit activity. -/
theorem no_eventual_positive_mass_floor :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m → c ≤ weightedMass (endpointCoeff (width m)) := by
  rintro ⟨c, hc, m₀, hlow⟩
  have hlt : ∀ᶠ m in atTop, weightedMass (endpointCoeff (width m)) < c :=
    (tendsto_order.1 weighted_mass_tendsto_zero).2 c hc
  obtain ⟨m, hmlt, hm₀⟩ := (hlt.and (eventually_ge_atTop m₀)).exists
  exact (not_le_of_gt hmlt) (hlow m hm₀)

end ManuscriptAudit.TentBoundaryActivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.TentBoundaryActivity.endpointCoeff_support,
    ``ManuscriptAudit.TentBoundaryActivity.endpointCoeff_unit_activity,
    ``ManuscriptAudit.TentBoundaryActivity.endpointCoeff_weighted_mass,
    ``ManuscriptAudit.TentBoundaryActivity.unit_activity_for_all,
    ``ManuscriptAudit.TentBoundaryActivity.weighted_mass_tendsto_zero,
    ``ManuscriptAudit.TentBoundaryActivity.no_eventual_positive_mass_floor] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
