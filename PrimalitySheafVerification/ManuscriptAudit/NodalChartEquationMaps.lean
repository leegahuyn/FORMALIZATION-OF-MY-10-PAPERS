import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PlaneEquationBaseChange
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralChartTransition

/-! The two literal nodal equations are preserved by coefficient homomorphisms. -/

namespace ManuscriptAudit.NodalChartCoefficientMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalIntegralChartTransition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 170000
set_option synthInstance.maxHeartbeats 14000

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem zEquation_map :
    PlaneEquationBaseChange.equation R S (zEquation R) = zEquation S := by
  simp only [PlaneEquationBaseChange.equation, zEquation, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have h : PlaneEquationBaseChange.coeffMap R S ((X : Polynomial R) ^ 2 * (X + 1)) =
      X ^ 2 * (X + 1) := by
    change ((X : Polynomial R) ^ 2 * (X + 1)).map (algebraMap R S) =
      (X : Polynomial S) ^ 2 * (X + 1)
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
      Polynomial.map_one]
  rw [h]

theorem yEquation_map :
    PlaneEquationBaseChange.equation R S (yEquation R) = yEquation S := by
  simp only [PlaneEquationBaseChange.equation, yEquation, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have hx : PlaneEquationBaseChange.coeffMap R S (X : Polynomial R) = X :=
    Polynomial.map_X _
  have hq : PlaneEquationBaseChange.coeffMap R S ((X : Polynomial R) ^ 2) = X ^ 2 := by
    rw [map_pow, hx]
  rw [hx, hq]


end
end ManuscriptAudit.NodalChartCoefficientMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartCoefficientMaps.zEquation_map,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yEquation_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
