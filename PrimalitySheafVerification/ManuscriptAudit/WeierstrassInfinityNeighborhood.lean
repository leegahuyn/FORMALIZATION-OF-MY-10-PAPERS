import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.OpenImmersion
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProperInfinityChart
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityOriginIdeal

/-! The literal infinity neighborhood of the proper Weierstrass closure
and its principal Cartier parameter. -/

namespace ManuscriptAudit.WeierstrassCartierInfinity

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassInfinityChartAlgebra
open WeierstrassInfinityOriginIdeal
open scoped nonZeroDivisors

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev linePoint := Spec (CommRingCat.of K)

abbrev neighborhoodScheme := Spec (CommRingCat.of (Neighborhood W))

def neighborhoodToChart : neighborhoodScheme W ⟶ WeierstrassInfinityChartImmersion.chartScheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring W) (Neighborhood W)))

/-- Open neighborhood of the actual infinity point on which its ideal is principal. -/
def neighborhoodOpen : neighborhoodScheme W ⟶ projectiveScheme W :=
  neighborhoodToChart W ≫ WeierstrassProperInfinityChart.chartOpen W

theorem neighborhoodOpen_isOpenImmersion : IsOpenImmersion (neighborhoodOpen W) := by
  letI : IsOpenImmersion (neighborhoodToChart W) := IsOpenImmersion.of_isLocalization (bracket W)
  unfold neighborhoodOpen
  infer_instance

def originToNeighborhood : linePoint (K := K) ⟶ neighborhoodScheme W :=
  Spec.map (CommRingCat.ofHom (localOrigin W).toRingHom)

/-- The ideal of the actual closed point on its open neighborhood is generated
by the regular function X/Y, hence gives an effective Cartier parameter. -/
theorem cartier_parameter :
    RingHom.ker (localOrigin W).toRingHom =
        Ideal.span ({localX W} : Set (Neighborhood W)) ∧
      localX W ∈ (Neighborhood W)⁰ :=
  ⟨localOrigin_ker W, WeierstrassInfinityChartRegular.localX_regular W⟩

end

end ManuscriptAudit.WeierstrassCartierInfinity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassCartierInfinity.neighborhoodOpen_isOpenImmersion,
      ``ManuscriptAudit.WeierstrassCartierInfinity.cartier_parameter] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
