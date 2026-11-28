import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor

/-! The actual principal divisor coefficient is the additive order of
the native height-one valuation. -/

namespace ManuscriptAudit.DedekindPrincipalOrder

open FractionalIdeal IsDedekindDomain WithZero DedekindPrincipalDivisor
open scoped nonZeroDivisors

noncomputable section

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R)

/-- The coefficient of a principal cycle is the true local order. -/
theorem principalDivisor_apply (x : Additive Fˣ) :
    principalDivisor R F x v = -log (v.valuation F (x.toMul : F)) := by
  classical
  let f : F := x.toMul
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := by
    intro hz
    apply x.toMul.ne_zero
    change f = 0
    rw [← he, hz, map_zero, zero_div]
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let i := algebraMap R F
  have ha' : i a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  have hb' : i b ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hb0
  have hsa : (Ideal.span ({a} : Set R)) ≠ 0 := by rwa [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
  have hsb : (Ideal.span ({b} : Set R)) ≠ 0 := by rwa [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
  have hm : spanSingleton R⁰ (i b) * spanSingleton R⁰ f = spanSingleton R⁰ (i a) := by
    rw [spanSingleton_mul_spanSingleton, ← he, mul_comm (i b), div_mul_cancel₀ (i a) hb']
  have hc := count_mul F v
    (spanSingleton_ne_zero_iff.mpr hb') (spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero)
  rw [hm, ← coeIdeal_span_singleton, ← coeIdeal_span_singleton, count_coe F v hsa, count_coe F v hsb] at hc
  change count F v (spanSingleton R⁰ f) = -log (v.valuation F f)
  rw [← he, Valuation.map_div, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg ha, v.intValuation_if_neg hb0,
    ← exp_sub, log_exp]
  rw [he]
  omega

end

end ManuscriptAudit.DedekindPrincipalOrder

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindPrincipalOrder.principalDivisor_apply
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
