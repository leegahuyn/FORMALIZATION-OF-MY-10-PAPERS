import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper7ActualCommonEuler

/-! The actual p. 280 quadratic denominators are nonvanishing along the full real axis. -/

namespace ManuscriptAudit.Paper7CommonEulerRealAxis

open Filter Topology Paper7ActualCommonEuler Paper7CommonEulerLocalDecay Paper7CommonEulerPointwise

theorem trace_sq_lt_four_prime {p : ℕ} (hp : p.Prime) (hfive : 5 ≤ p) (a : ℤ)
    (ha : |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ)) : (a : ℝ)^2 < 4 * (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpr : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hfive
  have hp0 : 0 < (p : ℝ) := by linarith
  have hs := Real.sq_sqrt hp0.le
  have hnonneg : 0 ≤ |(a : ℝ)| := abs_nonneg _
  have hsnonneg := Real.sqrt_nonneg (p : ℝ)
  have haSq : |(a : ℝ)|^2 ≤ (2 * Real.sqrt (p : ℝ))^2 := by gcongr
  rw [sq_abs] at haSq
  have hweak : (a : ℝ)^2 ≤ 4 * (p : ℝ) := by nlinarith only [haSq, hs]
  apply lt_of_le_of_ne hweak
  intro he
  have heZ : a^2 = 4 * (p : ℤ) := by exact_mod_cast he
  have heF := congrArg (fun z : ℤ => (z : ZMod p)) heZ
  have haF : (a : ZMod p)^2 = 0 := by
    simpa only [Int.cast_pow, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero] using heF
  have haF0 : (a : ZMod p) = 0 := by
    by_contra hn
    exact pow_ne_zero 2 hn haF
  have hdvd : (p : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp haF0
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at he
    norm_num at he
    linarith
  have habs : p ≤ a.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hdvd ha0
  have habsReal : (p : ℝ) ≤ |(a : ℝ)| := by
    have h := (show (p : ℝ) ≤ (a.natAbs : ℝ) by exact_mod_cast habs)
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsq : (p : ℝ)^2 ≤ |(a : ℝ)|^2 := by gcongr
  rw [sq_abs, he] at hsq
  have hcontra : (4 * (p : ℝ)) < (p : ℝ)^2 := by
    nlinarith only [mul_pos hp0 (show 0 < (p : ℝ) - 4 by linarith)]
  exact (not_lt_of_ge hsq) hcontra

theorem real_quadratic_pos {p : ℝ} (hp : 0 < p) {a : ℝ} (ha : a^2 < 4*p) (x : ℝ) :
    0 < 1 - a*x + p*x^2 := by
  have hp4 : 0 < 4*p := by positivity
  have hmul : 0 < (4*p) * (1 - a*x + p*x^2) := by
    calc
      0 < (2*p*x-a)^2 + (4*p-a^2) :=
        add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr ha)
      _ = (4*p) * (1 - a*x + p*x^2) := by ring
  by_contra! hn
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hp4.le hn)) hmul

theorem signedTrace_hasse_real (n : ℕ) :
    |(signedTrace n : ℝ)| ≤ 2 * Real.sqrt (goodPrime n : ℝ) := by
  have he : trace n = Complex.ofReal (signedTrace n : ℝ) := by
    simp only [trace, Complex.ofReal_intCast]
  simpa only [he, Complex.norm_real, Real.norm_eq_abs] using trace_hasse n

theorem all_actual_real_denominators_positive (n : ℕ) (x : ℝ) :
    0 < (denominator (goodPrime n) (trace n) x).re := by
  have hpr : (0 : ℝ) < goodPrime n := by
    exact_mod_cast (goodPrime_prime n).pos
  have hdisc := trace_sq_lt_four_prime (goodPrime_prime n) (goodPrime_atLeastFive n)
    (signedTrace n) (signedTrace_hasse_real n)
  have h : denominator (goodPrime n) (trace n) x =
      Complex.ofReal (1 - (signedTrace n : ℝ)*x + (goodPrime n : ℝ)*x^2) := by
    simp only [denominator, trace, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_intCast]
  rw [h, Complex.ofReal_re]
  exact real_quadratic_pos hpr hdisc x

theorem all_actual_real_denominators_nonzero (n : ℕ) (x : ℝ) :
    denominator (goodPrime n) (trace n) x ≠ 0 := by
  intro h
  have hp := all_actual_real_denominators_positive n x
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

/-- Even at honest nonzero real arguments, the actual finite products converge to zero. -/
theorem actual_product_tendsto_zero_on_real_axis {x : ℝ} (hx : x ≠ 0) :
    Tendsto (partialProduct goodPrime trace (x : ℂ)) atTop (𝓝 0) :=
  tendsto_at_nonzero goodPrime_tendsto trace_hasse (Complex.ofReal_ne_zero.mpr hx)

end ManuscriptAudit.Paper7CommonEulerRealAxis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.trace_sq_lt_four_prime,
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.real_quadratic_pos,
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.signedTrace_hasse_real,
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.all_actual_real_denominators_positive,
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.all_actual_real_denominators_nonzero,
      ``ManuscriptAudit.Paper7CommonEulerRealAxis.actual_product_tendsto_zero_on_real_axis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
