import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericQuotient

/-! The actual projective generic point lies in the native Cartier
puncture, and the puncture coordinate maps to the same rational parameter. -/

namespace ManuscriptAudit.WeierstrassGenericPuncture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassProjectiveGenericQuotient WeierstrassProjectiveGenericPoint
open WeierstrassInfinityPuncture WeierstrassInfinityOpenCover

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev N := Neighborhood W
private abbrev P := Puncture W
private abbrev F := W.FunctionField
private abbrev j := neighborhoodOpen W
private abbrev k := affineOpen W

local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W
local instance : Algebra (N W) (F W) := neighborhoodFractionAlgebra W
local instance : IsFractionRing (N W) (F W) := neighborhood_isFractionRing W

/-- The actual rational value of the Cartier coordinate is nonzero. -/
theorem parameter_ne_zero : algebraMap (N W) (F W) (localX W) ≠ 0 :=
  IsFractionRing.to_map_eq_zero_iff.not.mpr (localX_prime W).ne_zero

/-- The actual map of the native puncture into the function field. -/
def punctureToField : P W →+* F W :=
  IsLocalization.Away.lift (localX W) (g := algebraMap (N W) (F W))
    (isUnit_iff_ne_zero.mpr (parameter_ne_zero W))

theorem punctureToField_base (a : N W) :
    punctureToField W (algebraMap (N W) (P W) a) = algebraMap (N W) (F W) a := by
  unfold punctureToField
  exact IsLocalization.Away.lift_eq _ _ a

/-- The actual generic point lifted to the literal Mayer–Vietoris overlap. -/
def throughOverlap : genericScheme W ⟶ pullback (j W) (k W) :=
  pullback.lift (genericToNeighborhood W) (genericToAffine W)
    (genericPoint_factors_infinity W).symm

theorem genericPoint_factors_overlap :
    genericPoint W = throughOverlap W ≫ (pullback.fst (j W) (k W) ≫ j W) := by
  unfold throughOverlap
  rw [← Category.assoc, pullback.lift_fst]
  exact genericPoint_factors_infinity W

private theorem genericToPuncture_comm :
    Spec.map (CommRingCat.ofHom (punctureToField W)) ≫ punctureToNeighborhood W =
      genericToNeighborhood W := by
  unfold punctureToNeighborhood genericToNeighborhood
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (punctureToField_base W)

/-- Under the literal affine overlap identification, the generic point
is induced by its actual puncture ring map. -/
theorem throughOverlap_affine :
    throughOverlap W ≫ (overlapIso W).hom = Spec.map (CommRingCat.ofHom (punctureToField W)) := by
  apply (cancel_mono (punctureToNeighborhood W)).mp
  rw [Category.assoc, overlapIso_fac, genericToPuncture_comm, throughOverlap, pullback.lift_fst]

end

end ManuscriptAudit.WeierstrassGenericPuncture

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassGenericPuncture.punctureToField_base,
      ``ManuscriptAudit.WeierstrassGenericPuncture.throughOverlap_affine] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
