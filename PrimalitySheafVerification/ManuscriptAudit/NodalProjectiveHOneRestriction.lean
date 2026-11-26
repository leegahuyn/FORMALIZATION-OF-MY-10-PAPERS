import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.EtaleConstantHZeroRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisNontrivial
import PrimalitySheafVerification.ManuscriptAudit.KummerPrincipalOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisRestriction
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartPrincipalOpen

/-! Genuine restriction on étale H¹ of the proper nodal curve is detected by
its standard affine open. On the other chart a normal PID detects powers. -/

namespace ManuscriptAudit.NodalProjectiveHOneRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure NodalProperYChart NodalYChartImmersion
open NodalChartIntersection (charts_cover)
open NodalYChartPrincipalOpen
open EtaleTwoOpenHOne (openArrow)
open EtaleOpenIntersection (fstLeg sndLeg intersection_isPullback)
open EtaleMayerVietoris (openCoverSquare terminalCohomologyIso)
open OpenEtaleExtension

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev C := AddCommGrpCat.{0}
private abbrev A := AddCommGrpCat.of (ZMod 2)
private abbrev J := (projectiveNode K).smallEtaleTopology
private abbrev F := (constantSheaf (J K) C).obj A

private def rootLabelIso [NeZero (2 : K)] :
    KummerConstantCoefficients.coefficientGroup K 2 ≅ A := by
  let e := CuspRootCoefficients.rootsOfUnityEquivZMod K 2
  let e' : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    e.toAdditive
  exact e'.toAddCommGrpIso

private theorem yChart_restriction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (((F K).cohomologyPresheaf 1).map
      (sndLeg (affineOpen K) (chartOpen K)).op) := by
  letI : NeZero (2 : K) := ⟨h2⟩
  let j := chartOpen K
  let a := KummerRelativeUnitSections.chartArrow (principalRingHom K) j
  let e := (overlapEtaleIso K).hom
  have h : e ≫ a = sndLeg (affineOpen K) j := overlapEtaleIso_snd K
  let G := (constantSheaf (J K) C).obj (KummerConstantCoefficients.coefficientGroup K 2)
  let i := (Sheaf.cohomologyPresheafFunctor (J K) 1).mapIso
    ((constantSheaf (J K) C).mapIso (rootLabelIso K).symm)
  let U := op (Scheme.Etale.mk j)
  let V := op (principalObject K)
  have hG : Function.Injective ((G.cohomologyPresheaf 1).map a.op) :=
    KummerPrincipalOpenRestriction.restriction_constant_injective (projectiveNodeToBase K) j
      (xCoeff K) (coordinate_ne_zero K) 2 (by decide)
  have hF : Function.Injective (((F K).cohomologyPresheaf 1).map a.op) := by
    intro x y hxy
    apply ConcreteCategory.injective_of_mono (i.hom.app U)
    apply hG
    have hx := ConcreteCategory.congr_hom (i.hom.naturality a.op) x
    have hy := ConcreteCategory.congr_hom (i.hom.naturality a.op) y
    exact hx.symm.trans ((congrArg (i.hom.app V) hxy).trans hy)
  rw [← h, op_comp, Functor.map_comp]
  exact (ConcreteCategory.injective_of_mono
    (((F K).cohomologyPresheaf 1).map e.op)).comp hF

private theorem affine_restriction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (((F K).cohomologyPresheaf 1).map (openArrow (affineOpen K)).op) := by
  let j := affineOpen K
  let k := chartOpen K
  let l := pullback.fst j k ≫ j
  letI : PreconnectedSpace (overlapObject K).left := overlap_preconnected K
  letI : Nonempty (overlapObject K).left := overlap_nonempty K
  have hc : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun W : (projectiveNode K).Opens => (W : Set (projectiveNode K))) (charts_cover K)
  let S := openCoverSquare j k l (fstLeg j k) (sndLeg j k) (intersection_isPullback j k) hc
  have hLower : Function.Surjective (((F K).cohomologyPresheaf 0).map (fstLeg j k).op) :=
    EtaleConstantHZeroRestriction.restriction_surjective A (fstLeg j k)
  exact MayerVietorisRestriction.first_restriction_injective S (F K) 0
    hLower (yChart_restriction_injective K h2)

/-- Ordinary degree one of the proper node injects into that of its actual affine chart. -/
def restriction :
    Sheaf.H (F K) 1 →+
      Sheaf.H ((constantSheaf (affineNode K).smallEtaleTopology C).obj A) 1 := by
  let j := affineOpen K
  let e₀ := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv j (F K) 1
  let e₂ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app A)).addCommGroupIsoToAddEquiv
  exact (e₁.trans e₂).toAddMonoidHom.comp
    ((((F K).cohomologyPresheaf 1).map (openArrow j).op).hom.comp e₀.symm.toAddMonoidHom)

/-- The native restriction in ordinary étale cohomology is injective. -/
theorem restriction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (restriction K) := by
  let j := affineOpen K
  let e₀ := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv j (F K) 1
  let e₂ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app A)).addCommGroupIsoToAddEquiv
  exact (e₁.trans e₂).injective.comp
    ((affine_restriction_injective K h2).comp e₀.symm.injective)

end
end ManuscriptAudit.NodalProjectiveHOneRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProjectiveHOneRestriction.restriction_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
