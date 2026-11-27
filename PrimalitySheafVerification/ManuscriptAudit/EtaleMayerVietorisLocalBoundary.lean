import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalSection
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundaryAdditive

/-! An additive comparison from actual quotient sections to the first
ambient chart, with the native liftability and overlap-zero criteria. -/

namespace ManuscriptAudit.EtaleMayerVietorisLocalBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleOpenIntersection EtaleTwoOpenHOne OpenEtaleExtension
open OpenEtaleExtendShortExact EtaleMayerVietoris
open SheafPresheafHOneBoundary SheafPresheafHOneBoundaryAdditive

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] OpenEtaleExtension.restriction_additive

universe u

private abbrev G := AddCommGrpCat.{u}
private abbrev E (X : Scheme.{u}) := Sheaf X.smallEtaleTopology G.{u}

variable {U V X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual local quotient sections give additive boundary classes on
the ambient copy of the open chart. -/
def localBoundaryMap
    (F : E X) (S : ShortComplex (E U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F) :
    S.X₃.obj.obj (op (identityObject U)) →+ F.H' 1 (Scheme.Etale.mk j) :=
  let T := extended j S F e
  let hT := extended_shortExact j S F e hS
  let φ := restrictedExtensionIso j S F e hS
  let A := (etalePostcompose j).obj (identityObject U)
  let q := postcomposeTerminalIso j
  ((F.cohomologyPresheaf 1).map q.inv.op).hom.comp
    ((boundaryAddHom X.smallEtaleTopology T hT A).comp
      (φ.hom.τ₃.hom.app (op (identityObject U))).hom)

/-- This additive boundary vanishes precisely for quotient sections
which lift on the actual first open. -/
theorem localBoundaryMap_zero_iff
    (F : E X) (S : ShortComplex (E U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F) (s : S.X₃.obj.obj (op (identityObject U))) :
    localBoundaryMap j F S hS e s = 0 ↔ SectionHasLift S (identityObject U) s := by
  let T := extended j S F e
  let hT := extended_shortExact j S F e hS
  let φ := restrictedExtensionIso j S F e hS
  let A := (etalePostcompose j).obj (identityObject U)
  let t : T.X₃.obj.obj (op A) := φ.hom.τ₃.hom.app (op (identityObject U)) s
  let q := postcomposeTerminalIso j
  let i := ((F.cohomologyPresheaf 1).mapIso q.op.symm).addCommGroupIsoToAddEquiv
  change i (boundaryOfSection X.smallEtaleTopology T hT A t) = 0 ↔ _
  rw [← map_zero i, i.injective.eq_iff,
    boundaryOfSection_eq_zero_iff X.smallEtaleTopology T hT A t]
  change SectionHasLift (T.map (restriction j G.{u})) (identityObject U)
    (φ.hom.τ₃.hom.app (op (identityObject U)) s) ↔ _
  exact sectionHasLift_iso φ (identityObject U) s

variable (k : V ⟶ X) [IsOpenImmersion k]

/-- If the quotient section lifts on the actual overlap, the additive
boundary class has zero overlap restriction. -/
theorem localBoundaryMap_overlap_zero
    (F : E X) (S : ShortComplex (E U)) (hS : S.ShortExact)
    (e : S.X₁ ≅ (restriction j G.{u}).obj F) (s : S.X₃.obj.obj (op (identityObject U)))
    (hs : SectionHasLift S (Scheme.Etale.mk (pullback.fst j k))
      (S.X₃.obj.map (openArrow (pullback.fst j k)).op s)) :
    (F.cohomologyPresheaf 1).map (fstLeg j k).op (localBoundaryMap j F S hS e s) = 0 := by
  let T := extended j S F e
  let hT := extended_shortExact j S F e hS
  let φ := restrictedExtensionIso j S F e hS
  let W := Scheme.Etale.mk (pullback.fst j k)
  let A := (etalePostcompose j).obj (identityObject U)
  let D := intersection j k
  let b : W ⟶ identityObject U := openArrow (pullback.fst j k)
  let r : D ⟶ A := (etalePostcompose j).map b
  let t : T.X₃.obj.obj (op A) := φ.hom.τ₃.hom.app (op (identityObject U)) s
  have hr : SectionHasLift T D (T.X₃.obj.map r.op t) := by
    have hw : T.X₃.obj.map r.op t =
        φ.hom.τ₃.hom.app (op W) (S.X₃.obj.map b.op s) :=
      ConcreteCategory.congr_hom (φ.hom.τ₃.hom.naturality b.op).symm s
    rw [hw]
    change SectionHasLift (T.map (restriction j G.{u})) W
      (φ.hom.τ₃.hom.app (op W) (S.X₃.obj.map b.op s))
    exact (sectionHasLift_iso φ W (S.X₃.obj.map b.op s)).mpr hs
  let q := postcomposeTerminalIso j
  have hArrow : fstLeg j k ≫ q.inv = r := by
    rw [← postcompose_overlap_arrow j k, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hOp : q.inv.op ≫ (fstLeg j k).op = r.op := by rw [← op_comp, hArrow]
  change (F.cohomologyPresheaf 1).map (fstLeg j k).op
    ((F.cohomologyPresheaf 1).map q.inv.op
      (boundaryOfSection X.smallEtaleTopology T hT A t)) = 0
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hOp, boundaryOfSection_restrict]
  exact (boundaryOfSection_eq_zero_iff X.smallEtaleTopology T hT D _).mpr hr

end
end ManuscriptAudit.EtaleMayerVietorisLocalBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietorisLocalBoundary.localBoundaryMap_zero_iff,
      ``ManuscriptAudit.EtaleMayerVietorisLocalBoundary.localBoundaryMap_overlap_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
