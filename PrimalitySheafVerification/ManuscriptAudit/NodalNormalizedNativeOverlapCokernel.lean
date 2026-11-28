import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeKummerChartBoundaryPresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeCharts
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartUnitOrder
import PrimalitySheafVerification.ManuscriptAudit.AdditiveCokernelPresentation

/-! On the actual normalization the Y overlap restriction in native
Kummer degree one has cyclic cokernel, measured by order at the newly
removed point on the explicit polynomial localization. -/

namespace ManuscriptAudit.NodalNormalizedNativeOverlapCokernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (projectiveNodeToBase)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalNormalizedNativeCharts (yToNormalized)
open NodalYChartImmersion (nodeYChart yCoordinateRing)
open NodalYChartOverlap (overlapRing)
open NodalYChartPrincipalOpen (principalRingHom principalInclusion)
open NodalYChartNestedLocalization (overlapCoordinates overlapDenominator)
open NativeKummerChartBoundaryPresentation (S boundary boundary_surjective boundary_ker boundary_natural chartArrow)
open ProetaleHighOpenCohomology (liftedObject)
open ProetaleOpenLocalLifts (openObject)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

abbrev baseMap : normalizedNode K ⟶ Spec (CommRingCat.of K) :=
  normalizationMap K ≫ projectiveNodeToBase K

abbrev Y := liftedObject (openObject (yToNormalized K))
abbrev W := liftedObject (openObject (principalInclusion K ≫ yToNormalized K))
abbrev F (d : ℕ) := (S (normalizedNode K) d).X₁

/-- This is the higher-universe native cohomology presheaf's actual restriction. -/
abbrev restriction (d : ℕ) : (F K d).H' 1 (Y K) →+ (F K d).H' 1 (W K) :=
  (((F K d).cohomologyPresheaf 1).map
    ((ProetaleMayerVietorisSite.siteEquivalence (normalizedNode K)).functor.map
      (chartArrow (yToNormalized K) (principalRingHom K))).op).hom

private theorem overlap_PID : IsPrincipalIdealRing (overlapRing K) := by
  letI : IsPrincipalIdealRing (Localization.Away (overlapDenominator K)) :=
    PrincipalOpenEtaleHTwo.principalIdealRing K (overlapDenominator K)
  exact IsPrincipalIdealRing.of_surjective (overlapCoordinates K).symm
    (overlapCoordinates K).symm.surjective

set_option maxHeartbeats 5800000 in
/-- The quotient by restriction from the actual normalized Y chart is ZMod d. -/
def cokernelEquiv (d : ℕ) [NeZero d] [NeZero (d : K)] :
    (((F K d).H' 1 (W K) : Type 1) ⧸ (restriction K d).range) ≃+ ZMod d := by
  letI := overlap_PID K
  let k := baseMap K
  let j := yToNormalized K
  let f := principalRingHom K
  let j' := principalInclusion K ≫ j
  let i := (ringUnits.map f).hom
  let u := boundary k j d
  let v := boundary k j' d
  let r := restriction K d
  let e : (((F K d).H' 1 (W K) : Type 1) ⧸ r.range) ≃+
      (Additive (overlapRing K)ˣ ⧸ (i.range ⊔ v.ker)) :=
    AdditiveCokernelPresentation.cokernelEquiv i u v r
      (boundary_surjective k j d) (boundary_surjective k j' d) (boundary_natural k j d f)
  have hKer : v.ker = (CyclicOrderQuotient.nsmulMap (B := Additive (overlapRing K)ˣ) d).range :=
    boundary_ker k j' d
  have e' : (((F K d).H' 1 (W K) : Type 1) ⧸ r.range) ≃+
      (Additive (overlapRing K)ˣ ⧸
        (i.range ⊔ (CyclicOrderQuotient.nsmulMap (B := Additive (overlapRing K)ˣ) d).range)) := by
    rw [← hKer]
    exact e
  exact e'.trans (CyclicOrderQuotient.quotientEquiv i (NodalYChartUnitOrder.order K)
    (NodalYChartUnitOrder.restriction_order_exact K) (NodalYChartUnitOrder.order_surjective K) d)

end
end ManuscriptAudit.NodalNormalizedNativeOverlapCokernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizedNativeOverlapCokernel.cokernelEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
