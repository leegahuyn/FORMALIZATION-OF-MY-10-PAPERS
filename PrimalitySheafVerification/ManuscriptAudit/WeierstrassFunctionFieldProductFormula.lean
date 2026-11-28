import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFractionalIdealDegree
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityAdicOrder

/-! Product formula for the actual function field of a smooth geometric
Weierstrass curve, including its unique rational point at infinity. -/

namespace ManuscriptAudit.WeierstrassFunctionFieldProductFormula

open FractionalIdeal WithZero WeierstrassCurve.Affine
open WeierstrassAffineIdealDegree WeierstrassFractionalIdealDegree WeierstrassInfinityAdicOrder
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev im := algebraMap (A W) (F W)
private abbrev Fractional := FractionalIdeal (A W)⁰ (F W)

local instance : IsDedekindDomain (A W) :=
  WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W

/-- The degree of a principal fractional ideal is the difference of the
actual affine degrees of its numerator and denominator. -/
theorem fractionalDegree_principal_ratio (a b : A W) (ha : a ≠ 0) (hb : b ≠ 0) :
    fractionalDegree W (spanSingleton (A W)⁰ (im W a / im W b)) =
      (degree W (Ideal.span {a}) : ℤ) - degree W (Ideal.span {b}) := by
  have ha' : im W a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  have hb' : im W b ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hb
  refine fractionalDegree_eq W
    (spanSingleton_ne_zero_iff.mpr (div_ne_zero ha' hb')) hb ?_
  change ((Ideal.span {a} : Ideal (A W)) : Fractional W) =
    spanSingleton (A W)⁰ (im W b) * spanSingleton (A W)⁰ (im W a / im W b)
  rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, mul_comm (im W b),
    div_mul_cancel₀ (im W a) hb']

/-- The native infinity valuation and native affine fractional-ideal
degree cancel in the divisor of any actual nonzero rational function. -/
theorem native_product_formula (f : F W) (hf : f ≠ 0) :
    fractionalDegree W (spanSingleton (A W)⁰ f) + (-log (functionFieldValuation W f)) = 0 := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A W) f
  have ha : a ≠ 0 := by
    intro hz
    apply hf
    rw [← h, hz, map_zero, zero_div]
  rw [← h, valuation_functionField_ratio W a b ha hb, fractionalDegree_principal_ratio W a b ha hb,
    log_exp]
  exact add_neg_cancel _

end

end ManuscriptAudit.WeierstrassFunctionFieldProductFormula

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassFunctionFieldProductFormula.fractionalDegree_principal_ratio,
      ``ManuscriptAudit.WeierstrassFunctionFieldProductFormula.native_product_formula] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
