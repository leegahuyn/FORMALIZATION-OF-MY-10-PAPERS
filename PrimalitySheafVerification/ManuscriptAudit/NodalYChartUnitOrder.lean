import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartNestedLocalization
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenUnitOrderExact
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! The unit quotient from the true Y chart to the true overlap is measured by the order at infinity. -/

namespace ManuscriptAudit.NodalYChartUnitOrder

open AlgebraicGeometry CategoryTheory Polynomial
open KummerUnitsSheaf (ringUnits)
open NodalYChartImmersion (yCoordinateRing coordinateEquiv)
open NodalYChartOverlap (overlapRing)
open NodalYChartPrincipalOpen (principalRingHom)
open NodalYChartNestedLocalization
open PrincipalOpenUnitOrderExact (orderAtZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private theorem denominator_eval_zero : (denominator K).eval 0 ≠ 0 := by
  simp [denominator]

private theorem denominator_ne_zero : denominator K ≠ 0 := by
  intro h
  exact denominator_eval_zero K (by rw [h, Polynomial.eval_zero])

private def chartUnitEquiv :
    Additive (yCoordinateRing K)ˣ ≃+ Additive (Localization.Away (denominator K))ˣ :=
  (ringUnits.mapIso (coordinateEquiv K).toRingEquiv.toCommRingCatIso).addCommGroupIsoToAddEquiv

private def overlapUnitEquiv :
    Additive (overlapRing K)ˣ ≃+ Additive (Localization.Away (overlapDenominator K))ˣ :=
  (ringUnits.mapIso (overlapCoordinates K).toRingEquiv.toCommRingCatIso).addCommGroupIsoToAddEquiv

private theorem unit_map_commutes (u : Additive (yCoordinateRing K)ˣ) :
    overlapUnitEquiv K ((ringUnits.map (principalRingHom K)) u) =
      PrincipalOpenUnitOrderExact.restriction K (denominator K) (chartUnitEquiv K u) := by
  apply Additive.ext
  apply Units.ext
  exact RingHom.congr_fun (overlapCoordinates_restriction K) (u.toMul : yCoordinateRing K)

/-- The integer order on actual overlap units in the Y coordinate. -/
def order : Additive (overlapRing K)ˣ →+ ℤ :=
  (orderAtZero K (denominator K) (denominator_ne_zero K)).comp (overlapUnitEquiv K).toAddMonoidHom

variable [IsAlgClosed K]

theorem order_surjective : Function.Surjective (order K) :=
  (PrincipalOpenUnitOrderExact.orderAtZero_surjective K (denominator K) (denominator_ne_zero K)).comp
    (overlapUnitEquiv K).surjective

theorem restriction_order_exact :
    Function.Exact (ringUnits.map (principalRingHom K)).hom (order K) := by
  intro u
  let e := overlapUnitEquiv K
  let f := denominator K
  constructor
  · intro h
    have h' : orderAtZero K f (denominator_ne_zero K) (e u) = 0 := h
    obtain ⟨v, hv⟩ :=
      (PrincipalOpenUnitOrderExact.restriction_order_exact K f (denominator_eval_zero K) (e u)).mp h'
    obtain ⟨v', rfl⟩ := (chartUnitEquiv K).surjective v
    exact ⟨v', e.injective ((unit_map_commutes K v').trans hv)⟩
  · rintro ⟨v, rfl⟩
    change orderAtZero K f (denominator_ne_zero K) (e ((ringUnits.map (principalRingHom K)) v)) = 0
    rw [unit_map_commutes K v]
    exact (PrincipalOpenUnitOrderExact.restriction_order_exact K f (denominator_eval_zero K) _).mpr
      ⟨chartUnitEquiv K v, rfl⟩

end
end ManuscriptAudit.NodalYChartUnitOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartUnitOrder.order_surjective,
      ``ManuscriptAudit.NodalYChartUnitOrder.restriction_order_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
