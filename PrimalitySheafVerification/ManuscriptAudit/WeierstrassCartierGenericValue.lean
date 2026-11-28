import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassGenericPuncture
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericSectionValue
import PrimalitySheafVerification.ManuscriptAudit.EtaleAffineUnitNaturality
import PrimalitySheafVerification.ManuscriptAudit.PrimeLocalizationUnits

/-! The literal Cartier transition on the intersection has exactly the
rational value of the local infinity parameter. -/

namespace ManuscriptAudit.WeierstrassCartierGenericValue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassInfinityOpenCover WeierstrassInfinityPuncture WeierstrassGenericPuncture
open WeierstrassProjectiveGenericPoint WeierstrassProjectiveGenericQuotient
open OpenEtalePointSections OpenEtaleGenericSectionValue SmallEtaleBaseChange
open EtaleOpenIntersection KummerUnitsSheaf EtaleAffineUnitNaturality EtaleCohomologyPresheafZero

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev Y := projectiveScheme W
private abbrev L := Neighborhood W
private abbrev P := Puncture W
private abbrev F := W.FunctionField
private abbrev j := neighborhoodOpen W
private abbrev k := affineOpen W
private abbrev U := fullCoordinateUnitSheaf (Y W)
private abbrev D := (directImage (genericPoint W) AddCommGrpCat.{0}).obj
  (fullCoordinateUnitSheaf (genericScheme W))
private abbrev l := pullback.fst (j W) (k W) ≫ j W
private abbrev b := etaleBaseChange (genericPoint W)

local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W
local instance : Algebra (L W) (F W) := neighborhoodFractionAlgebra W

private abbrev T := Scheme.Etale.mk (l W)
private abbrev p := PrimeLocalizationUnits.primeUnit (localX W)

/-- The genuine local Cartier coordinate regarded as a rational unit. -/
def parameterUnit : Additive (F W)ˣ :=
  Additive.ofMul (Units.mk0 (algebraMap (L W) (F W) (localX W)) (parameter_ne_zero W))

/-- The actual prime transition in the ambient degree-zero group on the overlap. -/
def transitionClass : (U W).H' 0 (T W) :=
  (coordinateUnitEquiv (overlapIso W)).symm (Additive.ofMul (p W))

/-- The same transition in literal sections of the full coordinate-unit sheaf. -/
def transitionSection : (U W).obj.obj (op (T W)) :=
  equivZero (U W) (T W) (transitionClass W)

private def factoringLeft : IsTerminal ((b W).obj (Scheme.Etale.mk (j W))) := by
  unfold b
  rw [genericPoint_factors_infinity W]
  exact factoringOpen_isTerminal (genericToNeighborhood W) (j W)

private def factoringOverlap : IsTerminal ((b W).obj (T W)) := by
  unfold b
  rw [genericPoint_factors_overlap W]
  exact factoringOpen_isTerminal (throughOverlap W) (l W)

/-- The literal rational value of a generic section on the infinity neighborhood. -/
def leftValue : (D W).obj.obj (op (Scheme.Etale.mk (j W))) ≃+ Additive (F W)ˣ :=
  (genericValue (genericPoint W) (fullCoordinateUnitSheaf (genericScheme W))
    (Scheme.Etale.mk (j W)) (factoringLeft W)).trans
    (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of (F W)))).addCommGroupIsoToAddEquiv

private def overlapValue : (D W).obj.obj (op (T W)) ≃+ Additive (F W)ˣ :=
  (genericValue (genericPoint W) (fullCoordinateUnitSheaf (genericScheme W))
    (T W) (factoringOverlap W)).trans
    (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of (F W)))).addCommGroupIsoToAddEquiv

private theorem overlapValue_restrict (a : (D W).obj.obj (op (Scheme.Etale.mk (j W)))) :
    overlapValue W ((D W).obj.map (fstLeg (j W) (k W)).op a) = leftValue W a :=
  congrArg ((ringUnits.mapIso (Scheme.ΓSpecIso
    (CommRingCat.of (F W)))).addCommGroupIsoToAddEquiv)
    (genericValue_natural (genericPoint W) (fullCoordinateUnitSheaf (genericScheme W))
      (fstLeg (j W) (k W)) (factoringLeft W) (factoringOverlap W) a)

private theorem overlapGamma :
    (throughOverlap W).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (F W))).hom =
      (sectionIso (overlapIso W)).hom ≫ CommRingCat.ofHom (punctureToField W) := by
  let e := overlapIso W
  let g := throughOverlap W
  have h : g = Spec.map (CommRingCat.ofHom (punctureToField W)) ≫ e.inv := by
    rw [← throughOverlap_affine W, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (F W))).hom =
    (e.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (P W))).hom) ≫
      CommRingCat.ofHom (punctureToField W)
  rw [h, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]

private theorem transitionValue :
    overlapValue W ((regularToGeneric W).hom.app (op (T W)) (transitionSection W)) =
      parameterUnit W := by
  have h := genericValue_regular (genericPoint W) (l W) (throughOverlap W)
    (genericPoint_factors_overlap W) (factoringOverlap W) (transitionSection W)
  have hR := congrArg ((ringUnits.mapIso (Scheme.ΓSpecIso
    (CommRingCat.of (F W)))).addCommGroupIsoToAddEquiv) h
  have hQ : (sectionIso (overlapIso W)).hom.hom
      ((transitionSection W).toMul : Γ((T W).left, ⊤)) = ((p W : (P W)ˣ) : P W) :=
    congrArg (fun a : Additive (P W)ˣ => (a.toMul : P W))
      ((coordinateUnitEquiv (overlapIso W)).apply_symm_apply (Additive.ofMul (p W)))
  refine hR.trans ?_
  apply Additive.ext
  apply Units.ext
  have hΓ := congrArg (fun f : Γ((T W).left, ⊤) ⟶ CommRingCat.of (F W) =>
    f.hom ((transitionSection W).toMul : Γ((T W).left, ⊤))) (overlapGamma W)
  change _ = (punctureToField W) _ at hΓ
  rw [hQ, PrimeLocalizationUnits.primeUnit_val, punctureToField_base] at hΓ
  exact hΓ

/-- The rational unit determined by the actual transition lifts it on
the infinity neighborhood, with its native value explicitly recorded. -/
theorem exists_leftLift :
    ∃ a : (D W).obj.obj (op (Scheme.Etale.mk (j W))),
      leftValue W a = parameterUnit W ∧
      (D W).obj.map (fstLeg (j W) (k W)).op a =
        (regularToGeneric W).hom.app (op (T W)) (transitionSection W) := by
  let a := (leftValue W).symm (parameterUnit W)
  have ha : leftValue W a = parameterUnit W := (leftValue W).apply_symm_apply _
  refine ⟨a, ha, (overlapValue W).injective ?_⟩
  exact (overlapValue_restrict W a).trans (ha.trans (transitionValue W).symm)

end

end ManuscriptAudit.WeierstrassCartierGenericValue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassCartierGenericValue.exists_leftLift
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
