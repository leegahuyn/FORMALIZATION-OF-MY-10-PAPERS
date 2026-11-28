import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveDegreeArithmetic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveDivisorConnecting
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCartierDivisorSection
import PrimalitySheafVerification.ManuscriptAudit.DegreeOfConnectingClass

/-! The genuine projective étale unit cohomology has an integer degree
that sends the Cartier class at infinity to one. -/

namespace ManuscriptAudit.WeierstrassProjectiveDegree

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassProjectiveGenericPoint WeierstrassProjectiveGenericQuotient
open WeierstrassProjectiveGenericUnits WeierstrassProjectiveDivisorConnecting
open WeierstrassProjectiveCycleDegree WeierstrassProjectiveDegreeArithmetic
open WeierstrassCartierGenericValue WeierstrassCartierDivisorSection WeierstrassCartierBoundaryCohomology
open WeierstrassAffineCycleDegree AffineOpenQuotientCycleNaturality DedekindPrincipalDivisor
open OpenEtaleGenericSectionValue SmallEtaleBaseChange KummerUnitsSheaf EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev N := Neighborhood W
private abbrev F := W.FunctionField
private abbrev X := projectiveScheme W
private abbrev M := fullCoordinateUnitSheaf (genericScheme W)
private abbrev G := genericUnitImage W
private abbrev Q := quotient W
private abbrev k := affineOpen W
private abbrev j := neighborhoodOpen W
private abbrev f := genericPoint W
private abbrev π := cokernel.π (regularToGeneric W)
private abbrev P := (Q W).obj.obj (op (terminal W))
private abbrev R := (G W).obj.obj (op (terminal W))

local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W
local instance : IsDedekindDomain (A W) := WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W
local instance : IsDedekindDomain (N W) := WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W
local instance : Algebra (N W) (F W) := neighborhoodFractionAlgebra W
local instance : IsFractionRing (N W) (F W) := neighborhood_isFractionRing W

local instance : Algebra.FiniteType K (A W) :=
  inferInstanceAs (Algebra.FiniteType K (AdjoinRoot W.polynomial))

local instance : Algebra.FiniteType K (N W) :=
  inferInstanceAs (Algebra.FiniteType K (Localization.Away (bracket W)))

private def genericTerminal :
    IsTerminal ((etaleBaseChange (f W)).obj (terminal W)) := by
  let B := etaleBaseChange (f W)
  letI : PreservesFiniteLimits B := preservesFiniteLimits (f W)
  exact (MorphismProperty.Over.mkIdTerminal @Etale (X W)).isTerminalObj B (terminal W)

private abbrev fieldValue :=
  (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of (F W)))).addCommGroupIsoToAddEquiv

/-- Global rational-unit evaluation on the genuine projective curve. -/
def globalValue : R W ≃+ Additive (F W)ˣ :=
  (genericValue (f W) (M W) (terminal W) (genericTerminal W)).trans (fieldValue W)

private theorem globalValue_restrict {B : Type} [CommRing B] [Algebra B (F W)]
    (i : Spec (CommRingCat.of B) ⟶ X W) [IsOpenImmersion i]
    (hi : f W = Spec.map (CommRingCat.ofHom (algebraMap B (F W))) ≫ i) (z : R W) :
    openRationalValue B (F W) i (f W) hi ((G W).obj.map (openArrow i).op z) =
      globalValue W z :=
  congrArg (fieldValue W)
    (genericValue_natural (f W) (M W) (openArrow i) (genericTerminal W)
      (factoringOpenTerminal B (F W) i (f W) hi) z)

private theorem leftValue_eq (z : (G W).obj.obj (op (Scheme.Etale.mk (j W)))) :
    openRationalValue (N W) (F W) (j W) (f W) (genericPoint_factors_infinity W) z =
      leftValue W z := by
  have h : factoringOpenTerminal (N W) (F W) (j W) (f W) (genericPoint_factors_infinity W) =
      factoringLeft W := Subsingleton.elim _ _
  change (fieldValue W) (genericValue (f W) (M W) _
    (factoringOpenTerminal (N W) (F W) (j W) (f W) (genericPoint_factors_infinity W)) z) =
      (fieldValue W) (genericValue (f W) (M W) _ (factoringLeft W) z)
  rw [h]

private theorem project_affine (z : R W) :
    affineCycle W ((π W).hom.app (op (terminal W)) z) =
      principalDivisor (A W) (F W) (globalValue W z) := by
  change openQuotientCycle K (A W) (F W) (k W) (f W) rfl
    ((Q W).obj.map (openArrow (k W)).op ((π W).hom.app (op (terminal W)) z)) = _
  rw [← NatTrans.naturality_apply (π W).hom (openArrow (k W)).op z,
    openQuotientCycle_projection, globalValue_restrict]

private theorem project_neighborhood (z : R W) :
    neighborhoodCycle W ((π W).hom.app (op (terminal W)) z) =
      principalDivisor (N W) (F W) (globalValue W z) := by
  change openQuotientCycle K (N W) (F W) (j W) (f W) (genericPoint_factors_infinity W)
    ((Q W).obj.map (openArrow (j W)).op ((π W).hom.app (op (terminal W)) z)) = _
  rw [← NatTrans.naturality_apply (π W).hom (openArrow (j W)).op z,
    openQuotientCycle_projection, globalValue_restrict]

theorem degree_global_principal (z : R W) :
    sectionDegree W ((π W).hom.app (op (terminal W)) z) = 0 := by
  change cycleDegree W (affineCycle W _) + infinityMultiplicity W (neighborhoodCycle W _) = 0
  rw [project_affine, project_neighborhood]
  exact principalCycles_degree_zero W (globalValue W z)

private theorem connecting_ker_le_degree_ker : (connecting W).ker ≤ (sectionDegree W).ker := by
  intro x hx
  obtain ⟨z, hz⟩ := (connecting_eq_zero W x).1 hx
  change sectionDegree W x = 0
  rw [← hz]
  exact degree_global_principal W z

/-- Native degree on the cohomology of the proper Weierstrass curve. -/
def degree : (fullCoordinateUnitSheaf (X W)).H' 1 (terminal W) →+ ℤ :=
  DegreeOfConnectingClass.descendedDegree (connecting W) (connecting_surjective W)
    (sectionDegree W) (connecting_ker_le_degree_ker W)

private theorem cartier_section_degree :
    ∃ z : P W, connecting W z = boundaryClass W 1 ∧ sectionDegree W z = 1 := by
  obtain ⟨a, z, hval, hleft, hright, hconn⟩ := exists_cartierSection W
  refine ⟨z, hconn, ?_⟩
  have ha : affineCycle W z = 0 := by
    change openQuotientCycle K (A W) (F W) (k W) (f W) rfl
      ((Q W).obj.map (openArrow (k W)).op z) = 0
    rw [hright, map_zero]
  have hn : neighborhoodCycle W z = principalDivisor (N W) (F W) (parameterUnit W) := by
    change openQuotientCycle K (N W) (F W) (j W) (f W) (genericPoint_factors_infinity W)
      ((Q W).obj.map (openArrow (j W)).op z) = _
    rw [hleft, openQuotientCycle_projection, leftValue_eq W a, hval]
  change cycleDegree W (affineCycle W z) + infinityMultiplicity W (neighborhoodCycle W z) = 1
  rw [ha, hn, map_zero, zero_add]
  exact parameter_degree_one W

/-- The actual integer Cartier boundary is split by the genuine degree. -/
theorem degree_boundary : Function.LeftInverse (degree W) (boundaryClass W) := by
  obtain ⟨z, hconn, hd⟩ := cartier_section_degree W
  exact DegreeOfConnectingClass.descendedDegree_leftInverse _ _ _ _ _ z hconn hd

end

end ManuscriptAudit.WeierstrassProjectiveDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveDegree.degree_global_principal,
      ``ManuscriptAudit.WeierstrassProjectiveDegree.degree_boundary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
