import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisConductorZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveCyclicRestriction
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

/-! The native proper and affine nodal H¹ agree for every invertible cyclic coefficient order. -/

namespace ManuscriptAudit.NodalProjectiveCyclicHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open EtaleOpenIntersection (fstLeg sndLeg)
open EtaleTwoOpenHOne (openArrow)
open EtaleMayerVietoris (first_leg_zero_of_overlap_quotient_zero existsHOne_of_compatible_pair terminalCohomologyIso)
open OpenEtaleExtension EtaleContinuousMapSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

local instance (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev A := AddCommGrpCat.{0}
private abbrev coefficient (d : ℕ) := AddCommGrpCat.of (ZMod d)
abbrev C (X : Scheme.{0}) (d : ℕ) :=
  (constantSheaf X.smallEtaleTopology A).obj (coefficient d)

variable (d : ℕ) [NeZero (d : K)]

/-- Every affine conductor class vanishes on the actual overlap for any invertible cyclic order. -/
theorem affine_leg_eq_zero (h2 : (2 : K) ≠ 0) :
    (((C (projectiveNode K) d).cohomologyPresheaf 1).map
      (fstLeg (affineOpen K) (chartOpen K)).op).hom = 0 := by
  let M := coefficient d
  let j := affineOpen K
  let k := chartOpen K
  let S := sequence K M
  let ν := NodalNormalizationFiber.affineNormalization K
  let F := C (projectiveNode K) d
  let e : S.X₁ ≅ (restriction j A).obj F :=
    (constantSheafContinuousMapIso (affineNode K) M).symm ≪≫ ((restrictionConstantIso j).app M).symm
  let W := NodalProjectiveOverlapConductorEmpty.overlap K
  have hEmpty : IsEmpty (NodalNormalizationEtaleFibers.Conductor K W).left := by
    change IsEmpty (pullback (NodalProjectiveOverlapConductorEmpty.overlapMap K)
      (NodalAffineOrigin.originMap K) : Scheme.{0})
    exact NodalProjectiveOverlapConductorEmpty.overlap_conductor_isEmpty K
  have hW : Subsingleton (S.X₃.obj.obj (op W)) := by
    change Subsingleton (ContinuousMap (NodalNormalizationEtaleFibers.Conductor K W).left M)
    exact ⟨fun f g ↦ ContinuousMap.ext fun x ↦ (hEmpty.false x).elim⟩
  let L := NodalNormalizationFiber.affineLine K
  let eLine := ((Sheaf.functorH L.smallEtaleTopology 1).mapIso
    (constantSheafContinuousMapIso L M)).addCommGroupIsoToAddEquiv
  have hLineConst := SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K d
  have hLine : Subsingleton (Sheaf.H (continuousMapSheaf L M) 1) :=
    ⟨fun x y ↦ eLine.symm.injective (hLineConst.elim _ _)⟩
  have hM : Subsingleton (Sheaf.H S.X₂ 1) :=
    AffineEtaleMorphism.fullDirectImage_HOne_subsingleton
      (CommRingCat.of (NodalNormalizationFiber.A K)) (CommRingCat.of (NodalNormalizationFiber.B K))
      ν (continuousMapSheaf L M) hLine
  exact first_leg_zero_of_overlap_quotient_zero j k F S (sequence_shortExact K M h2) e hM hW

/-- Mayer–Vietoris lifts every affine class by giving it zero component on the Y chart. -/
theorem restriction_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (NodalProjectiveCyclicRestriction.restriction K d) := by
  let j := affineOpen K
  let k := chartOpen K
  let F := C (projectiveNode K) d
  let P := F.cohomologyPresheaf 1
  let e₀ := (terminalCohomologyIso F 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv j F 1
  let e₂ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app (coefficient d))).addCommGroupIsoToAddEquiv
  let e := e₁.trans e₂
  have hCover : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun W : (projectiveNode K).Opens ↦ (W : Set (projectiveNode K)))
      (NodalChartIntersection.charts_cover K)
  intro x
  let t := e.symm x
  have hPair : P.map (fstLeg j k).op t = P.map (sndLeg j k).op 0 := by
    have hZ : P.map (fstLeg j k).op t = 0 :=
      DFunLike.congr_fun (affine_leg_eq_zero K d h2) t
    exact hZ.trans (map_zero _).symm
  obtain ⟨z, hz, _⟩ := existsHOne_of_compatible_pair j k F hCover t 0 hPair
  refine ⟨e₀ z, ?_⟩
  change e (P.map (openArrow j).op (e₀.symm (e₀ z))) = x
  rw [e₀.symm_apply_apply, hz, e.apply_symm_apply]

/-- The native proper nodal group has one copy of the cyclic coefficients in degree one. -/
def projectiveHOneEquiv (h2 : (2 : K) ≠ 0) : Sheaf.H (C (projectiveNode K) d) 1 ≃+ ZMod d :=
  (AddEquiv.ofBijective (NodalProjectiveCyclicRestriction.restriction K d)
    ⟨NodalProjectiveCyclicRestriction.restriction_injective K d, restriction_surjective K d h2⟩).trans
      (NodalConductorAbelianHOne.affineCyclicHOneEquiv K h2 d).symm

end
end ManuscriptAudit.NodalProjectiveCyclicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveCyclicHOne.affine_leg_eq_zero,
      ``ManuscriptAudit.NodalProjectiveCyclicHOne.restriction_surjective,
      ``ManuscriptAudit.NodalProjectiveCyclicHOne.projectiveHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
