import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveCycleDegree
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCartierGenericValue
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityFieldCoordinateComparison
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFunctionFieldProductFormula
import PrimalitySheafVerification.ManuscriptAudit.DedekindValuationChangeField

/-! In the genuine projective divisor degree, finite and infinity orders
of a principal divisor cancel and the Cartier parameter has order one. -/

namespace ManuscriptAudit.WeierstrassProjectiveDegreeArithmetic

open IsDedekindDomain DedekindPrincipalDivisor DedekindPrincipalOrder WithZero
open WeierstrassInfinityChartAlgebra WeierstrassInfinityPuncture WeierstrassInfinityAdicOrder
open WeierstrassProjectiveGenericQuotient WeierstrassProjectiveCycleDegree WeierstrassAffineCycleDegree
open WeierstrassInfinityFunctionField WeierstrassInfinityFieldCoordinateComparison
open WeierstrassFunctionFieldProductFormula WeierstrassCartierGenericValue

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev N := Neighborhood W
private abbrev F := W.FunctionField
private abbrev L := FractionRing (N W)
private abbrev v := infinityPrime W

local instance : IsDedekindDomain (A W) := WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W
local instance : IsDedekindDomain (N W) := WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W
local instance : Algebra (N W) (F W) := neighborhoodFractionAlgebra W
local instance : IsFractionRing (N W) (F W) := neighborhood_isFractionRing W

private theorem native_infinity_valuation (f : F W) :
    (v W).valuation (F W) f = functionFieldValuation W f := by
  let e := functionFieldEquiv W
  have hb (a : N W) : e (algebraMap (N W) (F W) a) = algebraMap (N W) (L W) a :=
    e.apply_symm_apply _
  have h := (DedekindValuationChangeField.valuation_map (N W) (F W) (L W) e.toRingHom hb (v W) f).symm
  have he := congrArg (fun t : F W →+* L W => (v W).valuation (L W) (t f))
    (functionFieldEquiv_toRingHom_eq W)
  exact h.trans he

/-- The sum of the two actual principal-cycle contributions to the
projective degree vanishes for each native rational unit. -/
theorem principalCycles_degree_zero (f : Additive (F W)ˣ) :
    cycleDegree W (principalDivisor (A W) (F W) f) +
        infinityMultiplicity W (principalDivisor (N W) (F W) f) = 0 := by
  rw [cycleDegree_principal]
  change _ + principalDivisor (N W) (F W) f (v W) = 0
  rw [principalDivisor_apply, native_infinity_valuation]
  exact native_product_formula W _ f.toMul.ne_zero

/-- The literal local Cartier coordinate contributes one at infinity. -/
theorem parameter_degree_one :
    infinityMultiplicity W (principalDivisor (N W) (F W) (parameterUnit W)) = 1 := by
  change principalDivisor (N W) (F W) (parameterUnit W) (v W) = 1
  rw [principalDivisor_apply]
  change - log ((v W).valuation (F W) (algebraMap (N W) (F W) (localX W))) = 1
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    (v W).intValuation_singleton (localX_prime W).ne_zero rfl, log_exp, neg_neg]

end

end ManuscriptAudit.WeierstrassProjectiveDegreeArithmetic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveDegreeArithmetic.principalCycles_degree_zero,
      ``ManuscriptAudit.WeierstrassProjectiveDegreeArithmetic.parameter_degree_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
