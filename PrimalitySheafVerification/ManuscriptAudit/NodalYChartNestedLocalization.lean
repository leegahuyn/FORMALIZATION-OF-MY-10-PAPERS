import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartPrincipalOpen
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenDivisorNaturality

/-! In the Y parameter, the actual overlap removes the single additional point zero. -/

namespace ManuscriptAudit.NodalYChartNestedLocalization

open Polynomial NodalYChartImmersion
open NodalYChartOverlap (overlapRing)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

abbrev denominator : Polynomial K := 1 - Polynomial.X ^ 2
abbrev overlapDenominator : Polynomial K := denominator K * Polynomial.X

private instance coordinateLocalization :
    IsLocalization.Away (denominator K) (yCoordinateRing K) :=
  IsLocalization.isLocalization_of_algEquiv _ (coordinateEquiv K).symm

private instance overlapLocalization :
    IsLocalization.Away (overlapDenominator K) (overlapRing K) := by
  change IsLocalization.Away (denominator K * Polynomial.X)
    (Localization.Away (algebraMap (Polynomial K) (yCoordinateRing K) Polynomial.X))
  infer_instance

/-- The true overlap ring is the polynomial localization at X times the Y-chart denominator. -/
def overlapCoordinates :
    overlapRing K ≃ₐ[Polynomial K] Localization.Away (overlapDenominator K) :=
  IsLocalization.algEquiv (Submonoid.powers (overlapDenominator K)) _ _

abbrev open_le :
    PrimeSpectrum.basicOpen (overlapDenominator K) ≤ PrimeSpectrum.basicOpen (denominator K) :=
  PrimeSpectrum.basicOpen_mul_le_left (denominator K) Polynomial.X

/-- The actual restriction map is the ordinary nested-localization map in the Y parameter. -/
theorem overlapCoordinates_restriction :
    (overlapCoordinates K).toRingHom.comp (algebraMap (yCoordinateRing K) (overlapRing K)) =
      (AffineLineDivisor.restrictRing K (denominator K) (overlapDenominator K)
        (open_le K)).comp (coordinateEquiv K).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator K))
  apply RingHom.ext
  intro p
  change overlapCoordinates K (algebraMap (yCoordinateRing K) (overlapRing K)
    (algebraMap (Polynomial K) (yCoordinateRing K) p)) =
      AffineLineDivisor.restrictRing K (denominator K) (overlapDenominator K)
        (open_le K) (coordinateEquiv K (algebraMap (Polynomial K) (yCoordinateRing K) p))
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, AlgEquiv.commutes,
    AffineLineDivisor.restrictRing_algebraMap]

end
end ManuscriptAudit.NodalYChartNestedLocalization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalYChartNestedLocalization.overlapCoordinates_restriction
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
