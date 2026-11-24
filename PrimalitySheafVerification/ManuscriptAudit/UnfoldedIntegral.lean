import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Set

namespace ManuscriptAudit.Paper8J1

/-- At `β = 1`, the scalar integrand printed on physical PDF p. 364 is
not integrable even on `(0, 1)`. The proof works for all natural `n`. -/
theorem not_integrableOn_unfoldedBetaOne_Ioo (n : ℕ) :
    ¬ IntegrableOn (fun y : ℝ => y⁻¹ * Real.exp (-(4 * Real.pi * (n : ℝ)) * y))
      (Ioo 0 1) := by
  let a : ℝ := 4 * Real.pi * (n : ℝ)
  change ¬ IntegrableOn (fun y : ℝ => y⁻¹ * Real.exp (-a * y)) (Ioo 0 1)
  intro h
  have ha : 0 ≤ a :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg 4) Real.pi_pos.le) (Nat.cast_nonneg n)
  have hscaled := h.integrable.const_mul (Real.exp a)
  have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioo 0 1) := by
    apply hscaled.mono measurable_id.inv.aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
    intro y hy
    have hyinv : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.1.le
    have harg : -a ≤ -a * y := by
      calc
        -a = -a * 1 := (mul_one _).symm
        _ ≤ -a * y := mul_le_mul_of_nonpos_left hy.2.le (neg_nonpos.mpr ha)
    have hpos : 0 ≤ Real.exp a * (y⁻¹ * Real.exp (-a * y)) :=
      mul_nonneg (Real.exp_pos _).le (mul_nonneg hyinv (Real.exp_pos _).le)
    rw [Real.norm_of_nonneg hyinv, Real.norm_of_nonneg hpos]
    calc
      y⁻¹ = Real.exp a * (y⁻¹ * Real.exp (-a)) := by
        rw [mul_left_comm (Real.exp a) y⁻¹ (Real.exp (-a)),
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ Real.exp a * (y⁻¹ * Real.exp (-a * y)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hyinv)
          (Real.exp_pos _).le
  have hinterval : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hinv
  rcases intervalIntegrable_inv_iff.mp hinterval with h01 | hzero
  · exact zero_ne_one h01
  · apply hzero
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨le_rfl, zero_le_one⟩

/-- The unregularized integral asserted finite in §J.2 of Paper 8 diverges
at the lower endpoint. This is the `β = 1` case. -/
theorem not_integrableOn_unfoldedBetaOne (n : ℕ) :
    ¬ IntegrableOn (fun y : ℝ => y⁻¹ * Real.exp (-(4 * Real.pi * (n : ℝ)) * y))
      (Ioi 0) :=
  fun h => not_integrableOn_unfoldedBetaOne_Ioo n (h.mono_set fun _ hy => hy.1)

/-- The nonnegative extended integral is infinite. -/
theorem lintegral_unfoldedBetaOne_eq_top (n : ℕ) :
    (∫⁻ y in Ioi (0 : ℝ),
      ENNReal.ofReal (y⁻¹ * Real.exp (-(4 * Real.pi * (n : ℝ)) * y))) = ⊤ := by
  by_contra hfinite
  have hmeas : Measurable (fun y : ℝ =>
      y⁻¹ * Real.exp (-(4 * Real.pi * (n : ℝ)) * y)) :=
    measurable_id.inv.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
  have hnonneg : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ y⁻¹ * Real.exp (-(4 * Real.pi * (n : ℝ)) * y) :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun y hy => mul_nonneg (inv_nonneg.mpr hy.le) (Real.exp_pos _).le)
  exact not_integrableOn_unfoldedBetaOne n
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnonneg).2 (lt_top_iff_ne_top.mpr hfinite)⟩

end ManuscriptAudit.Paper8J1

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Paper8J1.not_integrableOn_unfoldedBetaOne_Ioo,
    ``ManuscriptAudit.Paper8J1.not_integrableOn_unfoldedBetaOne,
    ``ManuscriptAudit.Paper8J1.lintegral_unfoldedBetaOne_eq_top] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
