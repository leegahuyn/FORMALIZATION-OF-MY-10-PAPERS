import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneRestriction

/-! Actual proper-to-affine H¹ restriction is injective for every
invertible cyclic coefficient group over an algebraically closed field. -/

namespace ManuscriptAudit.NodalProjectiveCyclicRestriction

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

private abbrev Ab := AddCommGrpCat.{0}
private abbrev J := (projectiveNode K).smallEtaleTopology
private abbrev coeff (d : ℕ) := AddCommGrpCat.of (ZMod d)
private abbrev F (d : ℕ) := (constantSheaf (J K) Ab).obj (coeff d)

private def rootLabelIso (d : ℕ) [NeZero (d : K)] :
    KummerConstantCoefficients.coefficientGroup K d ≅ coeff d :=
  (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive.toAddCommGrpIso

private theorem chart_restriction_injective (d : ℕ) [NeZero (d : K)] :
    Function.Injective (((F K d).cohomologyPresheaf 1).map
      (sndLeg (affineOpen K) (chartOpen K)).op) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let j := chartOpen K
  let a := KummerRelativeUnitSections.chartArrow (principalRingHom K) j
  let e := (overlapEtaleIso K).hom
  have h : e ≫ a = sndLeg (affineOpen K) j := overlapEtaleIso_snd K
  let G := (constantSheaf (J K) Ab).obj (KummerConstantCoefficients.coefficientGroup K d)
  let i := (Sheaf.cohomologyPresheafFunctor (J K) 1).mapIso
    ((constantSheaf (J K) Ab).mapIso (rootLabelIso K d).symm)
  let U := op (Scheme.Etale.mk j)
  let V := op (principalObject K)
  have hG : Function.Injective ((G.cohomologyPresheaf 1).map a.op) :=
    KummerPrincipalOpenRestriction.restriction_constant_injective (projectiveNodeToBase K) j
      (xCoeff K) (coordinate_ne_zero K) d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hF : Function.Injective (((F K d).cohomologyPresheaf 1).map a.op) := by
    intro x y hxy
    apply (i.app U).addCommGroupIsoToAddEquiv.injective
    apply hG
    have hx := ConcreteCategory.congr_hom (i.hom.naturality a.op) x
    have hy := ConcreteCategory.congr_hom (i.hom.naturality a.op) y
    exact hx.symm.trans ((congrArg (i.hom.app V) hxy).trans hy)
  rw [← h, op_comp, Functor.map_comp]
  let e' := ((F K d).cohomologyPresheaf 1).mapIso (overlapEtaleIso K).op
  exact e'.addCommGroupIsoToAddEquiv.injective.comp hF

private theorem chart_affine_restriction_injective (d : ℕ) [NeZero (d : K)] :
    Function.Injective (((F K d).cohomologyPresheaf 1).map (openArrow (affineOpen K)).op) := by
  let j := affineOpen K
  let k := chartOpen K
  let l := pullback.fst j k ≫ j
  letI : PreconnectedSpace (overlapObject K).left := overlap_preconnected K
  letI : Nonempty (overlapObject K).left := overlap_nonempty K
  have hc : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun W : (projectiveNode K).Opens ↦ (W : Set (projectiveNode K))) (charts_cover K)
  let S := openCoverSquare j k l (fstLeg j k) (sndLeg j k) (intersection_isPullback j k) hc
  have hLower : Function.Surjective (((F K d).cohomologyPresheaf 0).map (fstLeg j k).op) :=
    EtaleConstantHZeroRestriction.restriction_surjective (coeff d) (fstLeg j k)
  exact MayerVietorisRestriction.first_restriction_injective S (F K d) 0 hLower
    (chart_restriction_injective K d)

/-- The actual ordinary restriction from the projective model to its affine node. -/
def restriction (d : ℕ) :
    Sheaf.H (F K d) 1 →+
      Sheaf.H ((constantSheaf (affineNode K).smallEtaleTopology Ab).obj (coeff d)) 1 := by
  let j := affineOpen K
  let e₀ := (terminalCohomologyIso (F K d) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv j (F K d) 1
  let e₂ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app (coeff d))).addCommGroupIsoToAddEquiv
  exact (e₁.trans e₂).toAddMonoidHom.comp
    ((((F K d).cohomologyPresheaf 1).map (openArrow j).op).hom.comp e₀.symm.toAddMonoidHom)

/-- The native proper-to-affine restriction is injective. -/
theorem restriction_injective (d : ℕ) [NeZero (d : K)] :
    Function.Injective (restriction K d) := by
  let j := affineOpen K
  let e₀ := (terminalCohomologyIso (F K d) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv j (F K d) 1
  let e₂ := ((Sheaf.functorH (affineNode K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso j).app (coeff d))).addCommGroupIsoToAddEquiv
  exact (e₁.trans e₂).injective.comp
    ((chart_affine_restriction_injective K d).comp e₀.symm.injective)

end

end ManuscriptAudit.NodalProjectiveCyclicRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProjectiveCyclicRestriction.restriction_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
