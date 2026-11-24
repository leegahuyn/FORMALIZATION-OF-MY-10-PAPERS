import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.ProjIcc

/-!
# Backward heat in the hypothesis of Paper 10, Theorem 4.4

Physical PDF pp. 487–488 allow the correction to have the same Sobolev order
as the leading elliptic operator. The positive diagonal rates below are those
of the Dirichlet sine basis on (0, π). The correction −2L is bounded between
the weighted H¹ and H⁻¹ spaces and reverses the sign of the total gradient.
This file proves failure of square summability in the infinite modal model.
Identifying a particular Γ(2) gauge energy and proving its H2/H3 properties
are separate obligations.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ManuscriptAudit.BackwardHeat

/-- The positive diagonal elliptic rates on the infinite sequence of modes. -/
def modeRate (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) ^ 2

noncomputable def initialMode (n : ℕ) : ℝ := (modeRate n)⁻¹

private theorem modeRate_pos (n : ℕ) : 0 < modeRate n :=
  sq_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n))

/-- The prescribed initial sequence has finite weighted H¹ energy. -/
theorem initialMode_summable_H1 :
    Summable (fun n => modeRate n * initialMode n ^ 2) := by
  have h : Summable initialMode := by
    exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2
      ((Real.summable_nat_pow_inv (p := 2)).2 (by decide))
  have heq : (fun n => modeRate n * initialMode n ^ 2) = initialMode := by
    funext n
    rw [pow_two (initialMode n)]
    change modeRate n * ((modeRate n)⁻¹ * (modeRate n)⁻¹) = (modeRate n)⁻¹
    rw [← mul_assoc, mul_inv_cancel₀ (modeRate_pos n).ne', one_mul]
  rw [heq]
  exact h

def linearPart (u : ℕ → ℝ) (n : ℕ) : ℝ := modeRate n * u n

def correction (u : ℕ → ℝ) (n : ℕ) : ℝ := -2 * linearPart u n

/-- The Lipschitz hypothesis permits a correction that reverses the linear part. -/
theorem linearPart_add_correction (u : ℕ → ℝ) (n : ℕ) :
    linearPart u n + correction u n = -linearPart u n := by
  unfold correction
  ring

/-- The squared H⁻¹ difference of the correction equals four times the
squared H¹ difference, mode by mode. -/
theorem correction_weighted_square (u v : ℕ → ℝ) (n : ℕ) :
    (correction u n - correction v n) ^ 2 / modeRate n =
      4 * (modeRate n * (u n - v n) ^ 2) := by
  apply (div_eq_iff (modeRate_pos n).ne').2
  unfold correction linearPart
  ring

/-- The correction is bounded from the weighted H¹ scale to its dual, with
squared norm ratio four for differences in the scale. -/
theorem correction_H1_to_Hminus1 {u v : ℕ → ℝ}
    (h : Summable (fun n => modeRate n * (u n - v n) ^ 2)) :
    Summable (fun n => (correction u n - correction v n) ^ 2 / modeRate n) ∧
      (∑' n, (correction u n - correction v n) ^ 2 / modeRate n) =
        4 * (∑' n, modeRate n * (u n - v n) ^ 2) := by
  simp_rw [correction_weighted_square u v]
  exact ⟨h.mul_left 4, h.tsum_mul_left 4⟩

/-- The exponential evolution fails square summability at each positive time. -/
theorem not_summable_growingMode_square {t : ℝ} (ht : 0 < t) :
    ¬ Summable (fun n => (initialMode n * Real.exp (modeRate n * t)) ^ 2) := by
  intro h
  have hconstant : Summable (fun _ : ℕ => t ^ 2) := by
    refine h.of_nonneg_of_le (fun _ => sq_nonneg t) ?_
    intro n
    have hexp : modeRate n * t ≤ Real.exp (modeRate n * t) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have hle : t ≤ initialMode n * Real.exp (modeRate n * t) := by
      calc
        t = initialMode n * (modeRate n * t) := by
          rw [initialMode, ← mul_assoc, inv_mul_cancel₀ (modeRate_pos n).ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (modeRate_pos n).le)
    simpa only [pow_two] using mul_le_mul hle hle ht.le (ht.le.trans hle)
  exact (sq_pos_of_pos ht).ne' ((summable_const_iff (β := ℕ) (t ^ 2)).1 hconstant)

private theorem value_of_mode_ode {u : ℝ → ℝ} {rate T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn u (Icc 0 T))
    (hODE : ∀ s ∈ Ioo 0 T, HasDerivAt u (rate * u s) s) :
    u T = u 0 * Real.exp (rate * T) := by
  let weighted : ℝ → ℝ := fun s => Real.exp (-rate * s) * u s
  have hExpCont : Continuous (fun s : ℝ => Real.exp (-rate * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hweightedCont : ContinuousOn weighted (Icc 0 T) :=
    hExpCont.continuousOn.mul hcont
  have hweightedDeriv : ∀ s ∈ Ioo 0 T, HasDerivAt weighted 0 s := by
    intro s hs
    have hExp : HasDerivAt (fun v : ℝ => Real.exp (-rate * v))
        (Real.exp (-rate * s) * -rate) s := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul (-rate)).exp
    have hcancel : (Real.exp (-rate * s) * -rate) * u s +
        Real.exp (-rate * s) * (rate * u s) = 0 := by ring
    simpa only [weighted, Pi.mul_def, hcancel] using hExp.mul (hODE s hs)
  obtain ⟨c, _, hSlope⟩ := exists_hasDerivAt_eq_slope weighted (fun _ => 0)
    hT hweightedCont hweightedDeriv
  have hSlope' : (0 : ℝ) = (weighted T - weighted 0) / T := by simpa using hSlope
  have hdiff : weighted T = weighted 0 :=
    sub_eq_zero.mp (by simpa using ((eq_div_iff hT.ne').mp hSlope').symm)
  have hweighted : Real.exp (-rate * T) * u T = u 0 := by
    simpa [weighted] using hdiff
  calc
    u T = (Real.exp (rate * T) * Real.exp (-rate * T)) * u T := by
      rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
    _ = u 0 * Real.exp (rate * T) := by rw [mul_assoc, hweighted, mul_comm]

/-- A continuous modal trajectory satisfying the backward heat equations with
this initial datum cannot have square-summable endpoint coefficients. -/
theorem no_squareSummable_modal_trajectory (u : ℝ → ℕ → ℝ) {T : ℝ} (hT : 0 < T)
    (hinit : ∀ n, u 0 n = initialMode n)
    (hcont : ∀ n, ContinuousOn (fun s => u s n) (Icc 0 T))
    (hODE : ∀ n, ∀ s ∈ Ioo 0 T, HasDerivAt (fun v => u v n) (modeRate n * u s n) s) :
    ¬ Summable (fun n => (u T n) ^ 2) := by
  have hformula : ∀ n, u T n = initialMode n * Real.exp (modeRate n * T) := by
    intro n
    rw [← hinit n]
    exact value_of_mode_ode hT (hcont n) (hODE n)
  simpa only [hformula] using not_summable_growingMode_square hT


private theorem hasDerivAt_of_mode_integral {u : ℝ → ℝ} {rate T s : ℝ}
    (hT : 0 < T) (hs : s ∈ Ioo 0 T)
    (hcont : ContinuousOn u (Icc 0 T))
    (hIntegral : ∀ t ∈ Icc 0 T, u t = u 0 + ∫ x in 0..t, rate * u x) :
    HasDerivAt u (rate * u s) s := by
  let rhs : ℝ → ℝ := IccExtend hT.le (fun x : Icc (0 : ℝ) T => rate * u x)
  have hOn : ContinuousOn (fun x : ℝ => rate * u x) (Icc 0 T) :=
    continuousOn_const.mul hcont
  have hrhs : Continuous rhs := hOn.restrict.Icc_extend'
  have hrhs_eq (x : ℝ) (hx : x ∈ Icc 0 T) : rhs x = rate * u x :=
    IccExtend_of_mem hT.le (fun x : Icc (0 : ℝ) T => rate * u x) hx
  have hnear : (fun t => u 0 + ∫ x in 0..t, rhs x) =ᶠ[𝓝 s] u := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    rw [hIntegral t ⟨ht.1.le, ht.2.le⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ht.1.le] at hx
    exact hrhs_eq x ⟨hx.1, hx.2.trans ht.2.le⟩
  have hderiv := (intervalIntegral.integral_hasDerivAt_right
    (hrhs.intervalIntegrable 0 s)
    hrhs.aestronglyMeasurable.stronglyMeasurableAtFilter hrhs.continuousAt).const_add (u 0)
  rw [hrhs_eq s ⟨hs.1.le, hs.2.le⟩] at hderiv
  exact hderiv.congr_of_eventuallyEq hnear.symm

/-- Failure of square summability also follows from the integrated modal
equations, the form supplied by testing a time-weak evolution against a
fixed spatial mode. -/
theorem no_squareSummable_integrated_modal_trajectory
    (u : ℝ → ℕ → ℝ) {T : ℝ} (hT : 0 < T)
    (hinit : ∀ n, u 0 n = initialMode n)
    (hcont : ∀ n, ContinuousOn (fun s => u s n) (Icc 0 T))
    (hIntegral : ∀ n, ∀ t ∈ Icc 0 T,
      u t n = u 0 n + ∫ x in 0..t, modeRate n * u x n) :
    ¬ Summable (fun n => (u T n) ^ 2) := by
  refine no_squareSummable_modal_trajectory u hT hinit hcont ?_
  intro n s hs
  exact hasDerivAt_of_mode_integral hT hs (hcont n) (hIntegral n)

end ManuscriptAudit.BackwardHeat

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.BackwardHeat.initialMode_summable_H1,
    ``ManuscriptAudit.BackwardHeat.linearPart_add_correction,
    ``ManuscriptAudit.BackwardHeat.correction_H1_to_Hminus1,
    ``ManuscriptAudit.BackwardHeat.no_squareSummable_modal_trajectory,
    ``ManuscriptAudit.BackwardHeat.no_squareSummable_integrated_modal_trajectory] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
