import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Paper 9 fixes a Schwartz test function on physical p. 415 and specifies
the tent profile on pp. 423–425. The printed tent has unequal one-sided
derivatives at zero for every positive width.
-/

namespace ManuscriptAudit.TentRegularity

open Set MeasureTheory

noncomputable section

/-- The actual test profile on physical p. 423. -/
def tent (T t : ℝ) : ℝ :=
  max 0 (T - |t|)

/-- The right-hand derivative at the apex. -/
theorem tent_right_derivative {T : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (tent T) (-1) (Icc 0 T) 0 := by
  have h : HasDerivAt (fun t : ℝ => T - t) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub T
  refine h.hasDerivWithinAt.congr_of_mem (fun t ht => ?_) ⟨le_rfl, hT.le⟩
  have h₀ : 0 ≤ t := ht.1
  have h₁ : 0 ≤ T - t := sub_nonneg.mpr ht.2
  rw [tent, abs_of_nonneg h₀, max_eq_right h₁]

/-- The left-hand derivative at the apex. -/
theorem tent_left_derivative {T : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (tent T) 1 (Icc (-T) 0) 0 := by
  have h : HasDerivAt (fun t : ℝ => T + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add T
  refine h.hasDerivWithinAt.congr_of_mem (fun t ht => ?_) ⟨(neg_neg_of_pos hT).le, le_rfl⟩
  have h₀ : t ≤ 0 := ht.2
  have h₁ : 0 ≤ T + t := by
    simpa only [add_comm, sub_neg_eq_add] using sub_nonneg.mpr ht.1
  rw [tent, abs_of_nonpos h₀, sub_neg_eq_add, max_eq_right h₁]

/-- The test profile is not differentiable at zero. -/
theorem tent_not_differentiableAt_zero {T : ℝ} (hT : 0 < T) :
    ¬ DifferentiableAt ℝ (tent T) 0 := by
  intro h
  have hright : deriv (tent T) 0 = -1 :=
    (uniqueDiffOn_Icc hT _ ⟨le_rfl, hT.le⟩).eq_deriv _
      h.hasDerivAt.hasDerivWithinAt (tent_right_derivative hT)
  have hleft : deriv (tent T) 0 = 1 :=
    (uniqueDiffOn_Icc (neg_neg_of_pos hT) _ ⟨(neg_neg_of_pos hT).le, le_rfl⟩).eq_deriv _
      h.hasDerivAt.hasDerivWithinAt (tent_left_derivative hT)
  have hcontra : (-1 : ℝ) = 1 := hright.symm.trans hleft
  norm_num at hcontra

/-- No real Schwartz function has this tent as its underlying function. -/
theorem tent_not_schwartz {T : ℝ} (hT : 0 < T) :
    ¬ ∃ f : SchwartzMap ℝ ℝ, (f : ℝ → ℝ) = tent T := by
  rintro ⟨f, hf⟩
  apply tent_not_differentiableAt_zero hT
  rw [← hf]
  exact f.differentiableAt

private theorem tent_continuous (T : ℝ) : Continuous (tent T) :=
  continuous_const.max (continuous_const.sub continuous_abs)

/-- The actual tent has total Lebesgue mass T². -/
theorem tent_integral {T : ℝ} (hT : 0 < T) : (∫ t : ℝ, tent T t) = T ^ 2 := by
  have hneg : -T ≤ (0 : ℝ) := neg_nonpos.mpr hT.le
  have hab : -T ≤ T := hneg.trans hT.le
  have hZero (t : ℝ) (ht : t ∉ Icc (-T) T) : tent T t = 0 := by
    have ht' : T ≤ |t| := le_of_not_ge (fun h => ht (abs_le.mp h))
    exact max_eq_left (sub_nonpos.mpr ht')
  have hSet : (∫ t in Icc (-T) T, tent T t) = ∫ t : ℝ, tent T t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hZero
  rw [← hSet, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((tent_continuous T).intervalIntegrable (-T) 0)
    ((tent_continuous T).intervalIntegrable 0 T)]
  have hLeft : (∫ t in (-T)..0, tent T t) = ∫ t in (-T)..0, T + t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hneg] at ht
    have h₀ : 0 ≤ T + t := by linarith [ht.1]
    rw [tent, abs_of_nonpos ht.2, sub_neg_eq_add, max_eq_right h₀]
  have hRight : (∫ t in 0..T, tent T t) = ∫ t in 0..T, T - t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    rw [tent, abs_of_nonneg ht.1, max_eq_right (sub_nonneg.mpr ht.2)]
  rw [hLeft, hRight,
    intervalIntegral.integral_add
      (continuous_const.intervalIntegrable (-T) 0) (continuous_id.intervalIntegrable (-T) 0),
    intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 T) (continuous_id.intervalIntegrable 0 T),
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    integral_id, integral_id]
  simp only [smul_eq_mul]
  ring

/-- At most 2r/T of the normalized tent mass lies in any interval of length 2r. -/
theorem tent_normalized_window_mass_le {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (t₀ : ℝ) :
    (∫ t in Icc (t₀ - r) (t₀ + r), tent T t) / (∫ t : ℝ, tent T t) ≤
      2 * r / T := by
  have hab : t₀ - r ≤ t₀ + r := by linarith
  rw [tent_integral hT, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hMono : (∫ t in (t₀ - r)..(t₀ + r), tent T t) ≤
      ∫ _ : ℝ in (t₀ - r)..(t₀ + r), T :=
    intervalIntegral.integral_mono_on hab
      ((tent_continuous T).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun t _ => max_le hT.le (sub_le_self T (abs_nonneg t)))
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show t₀ + r - (t₀ - r) = 2 * r by ring] at hMono
  calc
    _ ≤ (2 * r * T) / T ^ 2 :=
      div_le_div_of_nonneg_right hMono (sq_nonneg T)
    _ = _ := by
      field_simp [hT.ne'] <;> ring

/-- The threshold chosen in the manuscript admits arbitrarily little
normalized mass in any fixed window about the target parameter. -/
theorem paper9_large_tent_need_not_localize (t₀ r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ 2 * |t₀| + 1 ≤ T ∧
      (∫ t in Icc (t₀ - r) (t₀ + r), tent T t) / (∫ t : ℝ, tent T t) < ε := by
  let T := 2 * |t₀| + 2 + (2 * r) / ε
  have hNonneg : 0 ≤ (2 * r) / ε :=
    div_nonneg (mul_nonneg (by norm_num) hr) hε.le
  have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg t₀]
  have hsize : 2 * |t₀| + 1 ≤ T := by dsimp [T]; linarith
  have hSmall : (2 * r) / ε < T := by dsimp [T]; linarith [abs_nonneg t₀]
  have hSmall' : 2 * r < T * ε := (div_lt_iff₀ hε).1 hSmall
  have hRatio : (2 * r) / T < ε :=
    (div_lt_iff₀ hT).2 (by simpa only [mul_comm] using hSmall')
  exact ⟨T, hT, hsize, (tent_normalized_window_mass_le hT hr t₀).trans_lt hRatio⟩

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``tent_right_derivative, ``tent_left_derivative,
      ``tent_not_differentiableAt_zero, ``tent_not_schwartz, ``tent_integral,
      ``tent_normalized_window_mass_le, ``paper9_large_tent_need_not_localize] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.TentRegularity

