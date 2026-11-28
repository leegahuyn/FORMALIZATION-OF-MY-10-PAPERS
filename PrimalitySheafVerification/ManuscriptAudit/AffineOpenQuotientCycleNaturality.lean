import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleIntegralTerminal
import PrimalitySheafVerification.ManuscriptAudit.AffineGenericIntegralValue
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricQuotientAtIntegral
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericUnitQuotient
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives

/-! The genuine divisor quotient on an actual affine open has the native
principal cycle of the same rational unit fed into the ambient quotient. -/

namespace ManuscriptAudit.AffineOpenQuotientCycleNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
open AffineEtaleIntegralTerminal AffineGeometricQuotientAtIntegral
open AffineEtaleTensorOverlap AffineGeometricIntegralChartCoordinates
open OpenEtalePointSections OpenEtaleGenericSectionValue OpenEtaleGenericUnitComparison
open OpenEtaleGenericUnitQuotient OpenEtaleHOneByRepresentatives OpenEtaleExtension
open GenericEtaleUnitSections SmallEtaleBaseChange KummerUnitsSheaf EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev g := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev M := fullCoordinateUnitSheaf (Y F)
private abbrev T := identityObject (X A)
private abbrev U := integralTerminal A
private abbrev B := coordinateRing A (U A).obj
private abbrev Q₀ := genericPointUnitQuotient A F

variable {Z : Scheme.{0}} (j : X A ⟶ Z) [IsOpenImmersion j] (f : Y F ⟶ Z)

private abbrev Q := cokernel (pullbackToDirectImage f)
private abbrev R := restriction j AddCommGrpCat.{0}
private abbrev O := Scheme.Etale.mk j
private abbrev G := (directImage f AddCommGrpCat.{0}).obj (M F)

def factoringOpenTerminal (hf : f = g A F ≫ j) :
    IsTerminal ((etaleBaseChange f).obj (O A j)) := by
  subst f
  exact factoringOpen_isTerminal (g A F) j

private abbrev fieldValue := (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of F))).addCommGroupIsoToAddEquiv

/-- Native rational-unit evaluation on the given actual factoring open. -/
def openRationalValue (hf : f = g A F ≫ j) :
    (G F f).obj.obj (op (O A j)) ≃+ Additive Fˣ :=
  (genericValue f (M F) (O A j) (factoringOpenTerminal A F j f hf)).trans (fieldValue F)

private def quotientRestrictionIso (hf : f = g A F ≫ j) :
    (R A j).obj (Q F f) ≅ Q₀ A F := by
  subst f
  exact quotientIso j (g A F)

/-- The finite cycle obtained from the actual quotient on the specified
affine open, using the native integral terminal object. -/
def openQuotientCycle (hf : f = g A F ≫ j) :
    (Q F f).obj.obj (op (O A j)) ≃+ (HeightOneSpectrum A →₀ ℤ) := by
  let eval := (sheafSections (X A).smallEtaleTopology AddCommGrpCat.{0}).obj (op (T A))
  exact (sectionEquiv j (Q F f)).trans
    (((eval.mapIso (quotientRestrictionIso A F j f hf)).addCommGroupIsoToAddEquiv).trans
      (quotientCycle K A F (U A)))

private def terminalOpenIso : (etalePostcompose j).obj (T A) ≅ O A j :=
  MorphismProperty.Over.isoMk (Iso.refl (X A)) (by rfl)

private abbrev genericRestricted := genericUnitImage A F

private theorem leftProjection_onSection
    (x : (G F (g A F ≫ j)).obj.obj (op (O A j))) :
    (quotientRestrictionIso A F j (g A F ≫ j) rfl).hom.hom.app (op (T A))
      (sectionEquiv j (Q F (g A F ≫ j))
        ((cokernel.π (pullbackToDirectImage (g A F ≫ j))).hom.app (op (O A j)) x)) =
    (cokernel.π (genericPointUnitsHom A F)).hom.app (op (T A))
      ((genericUnitsIso j (g A F)).hom.hom.app (op (T A))
        (sectionEquiv j (G F (g A F ≫ j)) x)) := by
  rw [sectionEquiv_natural]
  exact congrArg (fun m : (R A j).obj (G F (g A F ≫ j)) ⟶ Q₀ A F =>
    m.hom.app (op (T A)) (sectionEquiv j (G F (g A F ≫ j)) x))
    (quotientIso_projection j (g A F))

set_option maxHeartbeats 1500000 in
/-- The literal quotient projection on the open gives the principal
cycle of the same rational unit. -/
theorem openQuotientCycle_projection (hf : f = g A F ≫ j)
    (x : (G F f).obj.obj (op (O A j))) :
    openQuotientCycle K A F j f hf
      ((cokernel.π (pullbackToDirectImage f)).hom.app (op (O A j)) x) =
    DedekindPrincipalDivisor.principalDivisor A F (openRationalValue A F j f hf x) := by
  subst f
  let I := U A
  let e := coordinateChartIso A I.obj I.property
  let eSpec := (Scheme.AffineEtale.Spec (X A)).map e.hom
  letI := coordinateAlgebra A I.obj
  letI := coordinateAlgebra_etale A I.obj
  let bR : Function.Bijective (algebraMap A (B A)) := terminal_algebraMap_bijective A
  let v := (genericUnitsIso j (g A F)).hom.hom.app (op (T A))
    (sectionEquiv j (G F (g A F ≫ j)) x)
  let w := (genericRestricted A F).obj.map eSpec.op v
  have hBase (a : B A) :
      algebraMap (B A) F a =
        algebraMap A F ((AffineGenericIntegralValue.baseEquiv A (B A) bR).symm a) := by
    have he : (AffineGenericIntegralValue.baseEquiv A (B A) bR).symm a = a := by
      apply (AffineGenericIntegralValue.baseEquiv A (B A) bR).injective
      rw [AlgEquiv.apply_symm_apply]
      exact (terminal_algebraMap A a).symm
    rw [he]
  have hPrincipal := AffineGenericIntegralValue.sectionDivisor_terminal A (B A) F bR hBase w
  let r := (etaleBaseChange (g A F)).map eSpec ≫
    ((factoringComparison j (g A F)).hom.app (T A)) ≫
    (etaleBaseChange (g A F ≫ j)).map (terminalOpenIso A j).hom
  have hW : w = (M F).obj.map r.op x := by
    change (M F).obj.map ((etaleBaseChange (g A F)).map eSpec).op
      ((M F).obj.map ((factoringComparison j (g A F)).hom.app (T A)).op
        ((M F).obj.map ((etaleBaseChange (g A F ≫ j)).map (terminalOpenIso A j).hom).op x)) = _
    simp only [r, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] <;> rfl
  have hV : AffineGenericIntegralValue.terminalValue A (B A) F bR w =
      openRationalValue A F j (g A F ≫ j) rfl x := by
    rw [hW]
    exact congrArg (fieldValue F) (genericValue_transport (g A F ≫ j) (M F) (g A F)
      (O A j) (algebraEtaleObject A (B A)) (factoringOpenTerminal A F j _ rfl)
      (AffineGenericIntegralValue.baseChangeTerminal A (B A) F bR) r x)
  change quotientCycle K A F I ((quotientRestrictionIso A F j (g A F ≫ j) rfl).hom.hom.app (op (T A))
    (sectionEquiv j (Q F (g A F ≫ j))
      ((cokernel.π (pullbackToDirectImage (g A F ≫ j))).hom.app (op (O A j)) x))) = _
  rw [leftProjection_onSection A F j x]
  exact (quotientCycle_projection K A F I v).trans (hPrincipal.trans (congrArg _ hV))

end

end ManuscriptAudit.AffineOpenQuotientCycleNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineOpenQuotientCycleNaturality.openQuotientCycle_projection
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
