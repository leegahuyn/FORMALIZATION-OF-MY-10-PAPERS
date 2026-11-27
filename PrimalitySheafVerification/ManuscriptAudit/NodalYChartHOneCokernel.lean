import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AdditiveCokernelPresentation
import PrimalitySheafVerification.ManuscriptAudit.KummerChartBoundaryPresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartUnitOrder
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleHTwo

/-! The actual degree-one Y-chart restriction to the nodal overlap has one cyclic cokernel. -/

namespace ManuscriptAudit.NodalYChartHOneCokernel

open AlgebraicGeometry CategoryTheory Opposite
open KummerRelativeUnitSections (chartArrow)
open KummerUnitsSheaf (ringUnits)
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)
open NodalProperYChart (chartOpen)
open NodalYChartPrincipalOpen (principalRingHom principalInclusion principalObject)
open NodalYChartNestedLocalization (overlapCoordinates overlapDenominator)
open NodalYChartOverlap (overlapRing)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

abbrev Y := Scheme.Etale.mk (chartOpen K)
abbrev F (d : ℕ) := (KummerRelativeFull.sequence (projectiveNode K) d).X₁

/-- The native Kummer degree-one restriction along the true overlap inclusion. -/
def restriction (d : ℕ) : (F K d).H' 1 (Y K) →+ (F K d).H' 1 (principalObject K) :=
  (((F K d).cohomologyPresheaf 1).map (chartArrow (principalRingHom K) (chartOpen K)).op).hom

private theorem overlap_PID : IsPrincipalIdealRing (overlapRing K) := by
  letI : IsPrincipalIdealRing (Localization.Away (overlapDenominator K)) :=
    PrincipalOpenEtaleHTwo.principalIdealRing K (overlapDenominator K)
  exact IsPrincipalIdealRing.of_surjective (overlapCoordinates K).symm
    (overlapCoordinates K).symm.surjective

variable [IsAlgClosed K]

/-- On the actual nodal Y chart, the cokernel is exactly the newly removed point's cyclic order. -/
def cokernelEquiv (d : ℕ) [NeZero (d : K)] (hd : 0 < d) :
    (((F K d).H' 1 (principalObject K) : Type) ⧸ (restriction K d).range) ≃+ ZMod d := by
  letI : IsPrincipalIdealRing (overlapRing K) := overlap_PID K
  let k := projectiveNodeToBase K
  let j := chartOpen K
  let f := principalRingHom K
  let j' := principalInclusion K ≫ j
  let i := (ringUnits.map f).hom
  let u := KummerChartBoundaryPresentation.boundary k j d hd
  let v := KummerChartBoundaryPresentation.boundary k j' d hd
  let r := restriction K d
  let e := AdditiveCokernelPresentation.cokernelEquiv i u v r
    (KummerChartBoundaryPresentation.boundary_surjective k j d hd)
    (KummerChartBoundaryPresentation.boundary_surjective k j' d hd)
    (KummerChartBoundaryPresentation.boundary_natural k j d hd f)
  have hKer : v.ker = (CyclicOrderQuotient.nsmulMap (B := Additive (overlapRing K)ˣ) d).range :=
    KummerChartBoundaryPresentation.boundary_ker k j' d hd
  have e' : (((F K d).H' 1 (principalObject K) : Type) ⧸ r.range) ≃+
      (Additive (overlapRing K)ˣ ⧸
        (i.range ⊔ (CyclicOrderQuotient.nsmulMap (B := Additive (overlapRing K)ˣ) d).range)) := by
    simpa only [hKer] using e
  exact e'.trans (CyclicOrderQuotient.quotientEquiv i (NodalYChartUnitOrder.order K)
    (NodalYChartUnitOrder.restriction_order_exact K) (NodalYChartUnitOrder.order_surjective K) d)

end
end ManuscriptAudit.NodalYChartHOneCokernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalYChartHOneCokernel.cokernelEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
