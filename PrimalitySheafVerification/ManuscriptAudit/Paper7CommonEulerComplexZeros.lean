import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerRealAxis

/-! The actual good-prime quadratic denominators have complex roots approaching zero. -/

namespace ManuscriptAudit.Paper7CommonEulerComplexZeros

open Filter Topology Paper7ActualCommonEuler Paper7CommonEulerLocalDecay

noncomputable section

/-- One of the two roots of the characteristic polynomial with trace a and determinant p. -/
def characteristicRoot (p a : ℝ) : ℂ :=
  ⟨a / 2, Real.sqrt (4*p-a^2) / 2⟩

theorem characteristicRoot_checks {p a : ℝ} (h : 0 ≤ 4*p-a^2) :
    characteristicRoot p a ^ 2 - (a : ℂ) * characteristicRoot p a + (p : ℂ) = 0 ∧
      ‖characteristicRoot p a‖^2 = p := by
  let z := characteristicRoot p a
  change z^2 - (a : ℂ)*z + (p : ℂ) = 0 ∧ ‖z‖^2 = p
  have hs := Real.sq_sqrt h
  have him : z.im^2 = (4*p-a^2)/4 := by
    change (Real.sqrt (4*p-a^2)/2)^2 = _
    rw [div_pow, hs]
    norm_num
  have hre : z.re = a/2 := rfl
  constructor
  · apply Complex.ext
    · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero, hre]
      nlinarith only [him]
    · simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero, hre]
      ring
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre]
    nlinarith only [him]

theorem actual_denominator_zero_at_inverse_sqrt (n : ℕ) :
    ∃ z : ℂ, denominator (goodPrime n) (trace n) z = 0 ∧
      ‖z‖ = (Real.sqrt (goodPrime n : ℝ))⁻¹ := by
  let p : ℝ := goodPrime n
  let a : ℝ := signedTrace n
  have hp : 0 < p := by
    change (0 : ℝ) < goodPrime n
    exact_mod_cast (goodPrime_prime n).pos
  have hpC : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hd : 0 ≤ 4*p-a^2 := sub_nonneg.mpr
    (Paper7CommonEulerRealAxis.trace_sq_lt_four_prime (goodPrime_prime n)
      (goodPrime_atLeastFive n) (signedTrace n)
      (Paper7CommonEulerRealAxis.signedTrace_hasse_real n)).le
  obtain ⟨he, hn⟩ := characteristicRoot_checks hd
  let w := characteristicRoot p a
  let z : ℂ := w / (p : ℂ)
  refine ⟨z, ?_, ?_⟩
  · have hc : (a : ℂ) = trace n := by simp only [a, trace, Complex.ofReal_intCast]
    have hpc : (p : ℂ) = (goodPrime n : ℂ) := by simp only [p, Complex.ofReal_natCast]
    rw [denominator, ← hc, ← hpc]
    change (1 : ℂ) - (a : ℂ)*(w/(p : ℂ)) + (p : ℂ)*(w/(p : ℂ))^2 = 0
    have hEq : (p : ℂ) *
        (1 - (a : ℂ)*(w/(p : ℂ)) + (p : ℂ)*(w/(p : ℂ))^2) =
        w^2 - (a : ℂ)*w + (p : ℂ) := by
      field_simp [hpC] <;> ring
    rw [he] at hEq
    exact (mul_eq_zero.mp hEq).resolve_left hpC
  · have hw : ‖w‖ = Real.sqrt p := by
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg p)).mp
      rw [Real.sq_sqrt hp.le]
      exact hn
    change ‖w / (p : ℂ)‖ = (Real.sqrt p)⁻¹
    rw [norm_div, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hp_eq : p = Real.sqrt p * Real.sqrt p := by
      simpa only [pow_two] using (Real.sq_sqrt hp.le).symm
    calc
      Real.sqrt p / p = Real.sqrt p / (Real.sqrt p * Real.sqrt p) :=
        congrArg (fun d => Real.sqrt p / d) hp_eq
      _ = (Real.sqrt p)⁻¹ := by field_simp [hs]

theorem eventually_actual_zero_inside {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∃ z : ℂ, ‖z‖ < r ∧ denominator (goodPrime n) (trace n) z = 0 := by
  have hrp : 0 < 2/r := by positivity
  have hlate : ∀ᶠ n in atTop, (2/r)^2 ≤ (goodPrime n : ℝ) :=
    (tendsto_atTop.mp goodPrime_tendsto) _
  filter_upwards [hlate] with n hn
  obtain ⟨z, hz, hnorm⟩ := actual_denominator_zero_at_inverse_sqrt n
  have hsq := Real.sqrt_le_sqrt hn
  rw [Real.sqrt_sq hrp.le] at hsq
  refine ⟨z, ?_, hz⟩
  rw [hnorm, ← one_div]
  apply (div_lt_iff₀ (hrp.trans_le hsq)).mpr
  have hh : 2 ≤ r * Real.sqrt (goodPrime n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hr).mp hsq
  linarith

/-- There is no disk at zero free of roots of every actual local denominator. -/
theorem no_common_zero_free_disk {r : ℝ} (hr : 0 < r) :
    ¬ ∀ n (z : ℂ), ‖z‖ < r → denominator (goodPrime n) (trace n) z ≠ 0 := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_actual_zero_inside hr)
  obtain ⟨z, hz, he⟩ := hN N le_rfl
  exact h N z hz he

end
end ManuscriptAudit.Paper7CommonEulerComplexZeros

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerComplexZeros.characteristicRoot_checks,
      ``ManuscriptAudit.Paper7CommonEulerComplexZeros.actual_denominator_zero_at_inverse_sqrt,
      ``ManuscriptAudit.Paper7CommonEulerComplexZeros.eventually_actual_zero_inside,
      ``ManuscriptAudit.Paper7CommonEulerComplexZeros.no_common_zero_free_disk] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
