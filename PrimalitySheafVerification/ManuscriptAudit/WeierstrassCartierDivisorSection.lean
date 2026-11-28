import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCartierGenericValue
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCartierBoundaryCohomology
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveDivisorConnecting
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisCokernelBoundaryLift

/-! The genuine Cartier boundary class is represented by an actual
projective quotient section with the precise local infinity parameter. -/

namespace ManuscriptAudit.WeierstrassCartierDivisorSection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassInfinityPuncture WeierstrassInfinityOpenCover WeierstrassCartierBoundaryCohomology
open WeierstrassProjectiveGenericQuotient WeierstrassProjectiveDivisorConnecting
open WeierstrassCartierGenericValue MayerVietorisCokernelBoundaryLift
open KummerUnitsSheaf EtaleCohomologyPresheafZero EtaleOpenIntersection EtaleAffineUnitNaturality

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev j := neighborhoodOpen W
private abbrev k := affineOpen W
local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W

private abbrev S := EtaleMayerVietoris.openCoverSquare (j W) (k W)
  (pullback.fst (j W) (k W) ≫ j W) (fstLeg (j W) (k W)) (sndLeg (j W) (k W))
  (intersection_isPullback (j W) (k W)) (cover W)

private abbrev F := fullCoordinateUnitSheaf (projectiveScheme W)
private abbrev G := WeierstrassProjectiveGenericUnits.genericUnitImage W
private abbrev m := regularToGeneric W

local instance : Mono (m W) := regularToGeneric_mono W
local instance : IsDomain (Neighborhood W) :=
  (WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W).toIsDomain

private theorem boundary_one :
    (S W).δ (F W) 0 1 rfl (transitionClass W) = boundaryClass W 1 := by
  change _ = (S W).δ (F W) 0 1 rfl
    ((coordinateUnitEquiv (overlapIso W)).symm
      (Additive.ofMul ((PrimeLocalizationUnits.primeUnit (localX W)) ^ (1 : ℤ))))
  rw [zpow_one]
  rfl

/-- An actual global quotient section represents the Cartier class of
infinity, with value one local parameter on the infinity chart and zero
on the usual affine chart. -/
theorem exists_cartierSection :
    ∃ (a : (G W).obj.obj (op (S W).X₂)) (z : (quotient W).obj.obj (op (terminal W))),
      leftValue W a = parameterUnit W ∧
      (quotient W).obj.map (S W).f₂₄.op z = (cokernel.π (m W)).hom.app (op (S W).X₂) a ∧
      (quotient W).obj.map (S W).f₃₄.op z = 0 ∧
      connecting W z = boundaryClass W 1 := by
  obtain ⟨a, ha, hw⟩ := exists_leftLift W
  obtain ⟨z, h₂, h₃, h₄⟩ := exists_cokernel_lift (S W) (m W) a (transitionSection W) hw
  refine ⟨a, z, ha, h₂, h₃, ?_⟩
  change connecting W z = _
  have ht : (equivZero (F W) (S W).X₁).symm (transitionSection W) = transitionClass W :=
    (equivZero (F W) (S W).X₁).symm_apply_apply _
  exact h₄.trans ((congrArg ((S W).δ (F W) 0 1 rfl) ht).trans (boundary_one W))

end

end ManuscriptAudit.WeierstrassCartierDivisorSection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassCartierDivisorSection.exists_cartierSection
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
