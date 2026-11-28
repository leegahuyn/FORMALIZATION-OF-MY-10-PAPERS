import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricQuotientProjection
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricIntegralChartCoordinates
import PrimalitySheafVerification.ManuscriptAudit.DedekindEtaleGenericDivisor

/-! Actual quotient cycles and actual principal divisors agree on all
integral affine objects of the geometric small étale site. -/

namespace ManuscriptAudit.AffineGeometricQuotientAtIntegral

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
open GenericEtaleUnitSections DedekindEtaleGenericDivisor
open AffineGeometricDivisorSheaf AffineGeometricDivisorSections AffineGeometricDivisorHom
open AffineGeometricDivisorFullExact AffineGeometricQuotientProjection
open AffineGeometricChartDivisorMap AffineGeometricIntegralChartCoordinates

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev siteSpec := Scheme.AffineEtale.Spec (X A)
private abbrev Q := genericPointUnitQuotient A F
private abbrev D := affineDivisorSheaf K A
private abbrev G := genericUnitImage A F
private abbrev J := Scheme.AffineEtale.topology (X A)
variable (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory)

private abbrev B := coordinateRing A U.obj
private abbrev eval := (sheafSections (J A) AddCommGrpCat.{0}).obj (op U.obj)
private abbrev compareSheaf :=
  (E A).inverse.mapIso (genericPointUnitQuotientIsoDivisor K A F) ≪≫ restrictionIso K A

/-- The local quotient section gives the native finite divisor cycle,
computed in the chosen actual coordinate algebra of the integral object. -/
def quotientCycle :
    (Q A F).obj.obj (op ((siteSpec A).obj U.obj)) ≃+ (HeightOneSpectrum (B A U) →₀ ℤ) := by
  letI := coordinateAlgebra A U.obj
  letI := coordinateAlgebra_etale A U.obj
  letI : IsDomain (B A U) := U.property
  let e := coordinateChartIso A U.obj U.property
  exact ((eval A U).mapIso (compareSheaf K A F)).addCommGroupIsoToAddEquiv.trans
    (((D K A).obj.mapIso e.op).addCommGroupIsoToAddEquiv.trans
      (chartSectionsEquiv K A (B A U)))

/-- The principal quotient produced by a genuine rational section has
the literal principal cycle in the chart's coordinate algebra. -/
theorem quotientCycle_projection (x : (G A F).obj.obj (op ((siteSpec A).obj U.obj))) :
    letI := coordinateAlgebra A U.obj
    letI := coordinateAlgebra_etale A U.obj
    letI : IsDomain (B A U) := U.property
    let e := coordinateChartIso A U.obj U.property
    quotientCycle K A F U ((cokernel.π (genericPointUnitsHom A F)).hom.app
        (op ((siteSpec A).obj U.obj)) x) =
      sectionDivisor A (B A U) F ((G A F).obj.map ((siteSpec A).map e.hom).op x) := by
  dsimp only
  letI := coordinateAlgebra A U.obj
  letI := coordinateAlgebra_etale A U.obj
  letI : IsDomain (B A U) := U.property
  let e := coordinateChartIso A U.obj U.property
  let D₀ := (D K A).obj
  let G₀ := ((E A).inverse.obj (G A F)).obj
  let T := op U.obj
  let r := (E A).inverse.map (cokernel.π (genericPointUnitsHom A F))
  let h := (compareSheaf K A F).hom
  let d := affineDivisorHom K A F
  have h₁ : h.hom.app T (r.hom.app T x) = d.hom.app T x :=
    congrArg (fun f => f.hom.app T x) (affine_quotient_projection K A F)
  have h₂ : d.hom.app T x =
      D₀.map e.inv.op (chartDivisorMap K A (B A U) F (G₀.map e.hom.op x)) :=
    congrArg (fun f => f x) (affineDivisorHom_app_integral K A F U)
  let y := G₀.map e.hom.op x
  change chartSectionsEquiv K A (B A U) (D₀.map e.hom.op (h.hom.app T (r.hom.app T x))) =
    sectionDivisor A (B A U) F y
  rw [h₁, h₂]
  have h₃ : D₀.map e.hom.op (D₀.map e.inv.op (chartDivisorMap K A (B A U) F y)) =
      chartDivisorMap K A (B A U) F y :=
    (D₀.mapIso e.op).inv_hom_id_apply _
  change chartSectionsEquiv K A (B A U)
      (D₀.map e.hom.op (D₀.map e.inv.op (chartDivisorMap K A (B A U) F y))) = _
  rw [h₃]
  exact (chartSectionsEquiv K A (B A U)).apply_symm_apply (sectionDivisor A (B A U) F y)

end

end ManuscriptAudit.AffineGeometricQuotientAtIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineGeometricQuotientAtIntegral.quotientCycle_projection
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
