import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityAdicOrder
import PrimalitySheafVerification.ManuscriptAudit.PrimeLocalizationUnits

/-! The order at the actual rational infinity point reads off the
integer boundary coefficient of a unit on the literal chart overlap. -/

namespace ManuscriptAudit.WeierstrassPunctureUnitOrder

open WithZero WeierstrassCurve.Affine
open WeierstrassInfinityChartAlgebra WeierstrassInfinityOriginIdeal
open WeierstrassInfinityPuncture WeierstrassInfinityOpenCover WeierstrassInfinityPoleCoordinates
open WeierstrassInfinityAdicOrder PrimeLocalizationUnits

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev N := Neighborhood W
private abbrev P := Puncture W
private abbrev s := localX W

local instance : IsDedekindDomain (N W) :=
  WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W

private theorem unit_nonzero (f : (P W)ˣ) : punctureValuation W (f : P W) ≠ 0 :=
  (Units.isUnit f).map (punctureValuation W) |>.ne_zero

/-- Order as an additive homomorphism on actual overlap units. -/
def order : Additive (P W)ˣ →+ ℤ where
  toFun f := -log (punctureValuation W (f.toMul : P W))
  map_zero' := by
    change -log (punctureValuation W (1 : P W)) = 0
    simp
  map_add' f g := by
    change -log (punctureValuation W ((f.toMul : P W) * (g.toMul : P W))) =
      -log (punctureValuation W (f.toMul : P W)) + -log (punctureValuation W (g.toMul : P W))
    rw [map_mul, log_mul (unit_nonzero W f.toMul) (unit_nonzero W g.toMul), neg_add]

/-- The true rational Cartier parameter has order one. -/
theorem order_parameter : order W (Additive.ofMul (primeUnit (s W))) = 1 := by
  change -log (punctureValuation W ((primeUnit (s W) : (P W)ˣ) : P W)) = 1
  rw [primeUnit_val, ← punctureX, valuation_parameter, log_exp, neg_neg]

/-- Actual units on the neighborhood extend across infinity and have zero order there. -/
theorem order_lift (v : (N W)ˣ) :
    order W (Additive.ofMul (mapUnit (s W) v)) = 0 := by
  have h : localOrigin W (v : N W) ≠ 0 := (v.isUnit.map (localOrigin W)).ne_zero
  change -log (punctureValuation W ((mapUnit (s W) v : (P W)ˣ) : P W)) = 0
  rw [mapUnit_val, valuation_nonzero_residue W _ h, log_one, neg_zero]

/-- The valuation recovers the integer of any genuine unit decomposition. -/
theorem order_lift_mul (v : (N W)ˣ) (n : ℤ) :
    order W (Additive.ofMul (mapUnit (s W) v * primeUnit (s W) ^ n)) = n := by
  change order W (Additive.ofMul (mapUnit (s W) v) +
    n • Additive.ofMul (primeUnit (s W))) = n
  rw [map_add, map_zsmul, order_lift, order_parameter, zero_add, zsmul_one]

/-- An actual overlap unit has zero order if and only if it extends
as an actual unit across the rational point at infinity. -/
theorem order_eq_zero_iff (f : (P W)ˣ) :
    order W (Additive.ofMul f) = 0 ↔ ∃ v : (N W)ˣ, mapUnit (s W) v = f := by
  constructor
  · intro h
    obtain ⟨v, n, hn⟩ := exists_lift_mul_zpow (s W) (localX_prime W) f
    rw [hn, order_lift_mul] at h
    refine ⟨v, ?_⟩
    rw [hn, h, zpow_zero, mul_one]
  · rintro ⟨v, rfl⟩
    exact order_lift W v

end

end ManuscriptAudit.WeierstrassPunctureUnitOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassPunctureUnitOrder.order_parameter,
      ``ManuscriptAudit.WeierstrassPunctureUnitOrder.order_lift_mul,
      ``ManuscriptAudit.WeierstrassPunctureUnitOrder.order_eq_zero_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
