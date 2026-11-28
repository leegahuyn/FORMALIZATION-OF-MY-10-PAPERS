import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCartierBoundaryCohomology
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisOneChart
import PrimalitySheafVerification.ManuscriptAudit.SplitIntegerBoundaryTorsion

/-! The actual right chart of the projective Weierstrass cover and its
integer Cartier kernel. The precise geometric input is bijectivity of
the native restriction from the infinity neighborhood to its overlap. -/

namespace ManuscriptAudit.WeierstrassProjectiveAffineExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityOpenCover
open WeierstrassCartierBoundaryCohomology KummerUnitsSheaf EtaleOpenIntersection
open PowerTateModule

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

local instance : IsOpenImmersion (neighborhoodOpen W) := neighborhoodOpen_isOpenImmersion W

private abbrev square := EtaleMayerVietoris.openCoverSquare (neighborhoodOpen W) (affineOpen W)
  (pullback.fst (neighborhoodOpen W) (affineOpen W) ≫ neighborhoodOpen W)
  (fstLeg (neighborhoodOpen W) (affineOpen W)) (sndLeg (neighborhoodOpen W) (affineOpen W))
  (intersection_isPullback (neighborhoodOpen W) (affineOpen W)) (cover W)

private abbrev F := fullCoordinateUnitSheaf (projectiveScheme W)
private abbrev H := (F W).H' 1 (square W).X₄
private abbrev A := (F W).H' 1 (square W).X₃

/-- The literal projective-to-affine native restriction in degree one. -/
abbrev affineRestriction : H W →+ A W := MayerVietorisOneChart.toRight (square W) (F W)

private abbrev neighborhoodRestriction :=
  (((F W).cohomologyPresheaf 1).map (square W).f₁₂.op).hom

/-- The native affine restriction is onto when the actual neighborhood
restriction is onto. -/
theorem affineRestriction_surjective (hn : Function.Surjective (neighborhoodRestriction W)) :
    Function.Surjective (affineRestriction W) :=
  MayerVietorisOneChart.toRight_surjective (square W) (F W) hn

/-- The native affine restriction has exactly the integer Cartier kernel
when the actual neighborhood restriction is injective. -/
theorem affineRestriction_kernel (hn : Function.Injective (neighborhoodRestriction W)) :
    (boundaryClass W).range = (affineRestriction W).ker := by
  calc
    _ = (((square W).toBiprod (F W) 1).hom).ker := boundaryClass_exact W
    _ = (((square W).δ (F W) 0 1 rfl).hom).range :=
      (((square W).sequence_exact (F W) 0 1 rfl).exact' 2 3 4).ab_range_eq_ker.symm
    _ = _ := (MayerVietorisOneChart.toRight_ker (square W) (F W) hn).symm

/-- An integer degree retraction on the actual Cartier class identifies
the compatible projective and affine unit Tate modules. -/
def affineRestrictionTateEquiv (hn : Function.Bijective (neighborhoodRestriction W))
    (d : H W →+ ℤ) (hd : Function.LeftInverse d (boundaryClass W))
    (l : ℕ) [Fact l.Prime] : Tate l (H W) ≃ₗ[ℤ_[l]] Tate l (A W) :=
  SplitIntegerBoundaryTorsion.tateEquiv (boundaryClass W) (affineRestriction W)
    (affineRestriction_kernel W hn.1) (affineRestriction_surjective W hn.2) d hd l

end

end ManuscriptAudit.WeierstrassProjectiveAffineExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveAffineExact.affineRestriction_surjective,
      ``ManuscriptAudit.WeierstrassProjectiveAffineExact.affineRestriction_kernel,
      ``ManuscriptAudit.WeierstrassProjectiveAffineExact.affineRestrictionTateEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
