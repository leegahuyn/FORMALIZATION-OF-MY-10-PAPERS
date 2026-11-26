import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalSection
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverFullTrace
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverOverlapObject

/-! The proper nodal cubic has a nonzero étale degree-one class with
Z/2 coefficients. The affine crossed cover gives a trace obstruction,
and the chosen sheet of the overlap makes this class extend. -/

namespace ManuscriptAudit.NodalProjectiveHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open NodalProjectiveClosure (affineNode projectiveNode affineOpen)
open NodalProperYChart (chartOpen)
open NodalChartIntersection (charts_cover)
open NodalSwapCoverOverlapObject (overlapAffineObject overlapAffineObjectIso overlapObjectSection)
open NodalSwapCoverFullTrace (shortComplex shortComplex_shortExact terminalOne terminal_one_unlifted
  constantIso fullTrace_app_surjective_of_section)
open EtaleMayerVietoris (SectionHasLift HOne_nontrivial_of_local_section_lift)
open OpenEtaleExtension (restriction restrictionConstantIso)
open EtaleTwoOpenHOne (identityObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev coeff := AddCommGrpCat.of (ZMod 2)
private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj coeff

private theorem chart_ranges_cover :
    Set.range (affineOpen K) ∪ Set.range (chartOpen K) = Set.univ :=
  congrArg (fun W : (projectiveNode K).Opens => (W : Set (projectiveNode K))) (charts_cover K)

private theorem terminal_unlifted (h2 : (2 : K) ≠ 0) :
    ¬ SectionHasLift (shortComplex K h2) (identityObject (affineNode K)) (terminalOne K) :=
  terminal_one_unlifted K h2

set_option maxHeartbeats 1700000 in
private theorem overlap_lifted (h2 : (2 : K) ≠ 0) :
    let W := Scheme.Etale.mk (pullback.fst (affineOpen K) (chartOpen K))
    SectionHasLift (shortComplex K h2) W
      ((shortComplex K h2).X₃.obj.map
        (openArrow (pullback.fst (affineOpen K) (chartOpen K))).op (terminalOne K)) := by
  let S := shortComplex K h2
  let W := Scheme.Etale.mk (pullback.fst (affineOpen K) (chartOpen K))
  let U := overlapAffineObject K
  let q := overlapAffineObjectIso K
  let t : S.X₃.obj.obj (op W) :=
    S.X₃.obj.map (openArrow (pullback.fst (affineOpen K) (chartOpen K))).op (terminalOne K)
  change SectionHasLift S W t
  obtain ⟨u, hu⟩ := fullTrace_app_surjective_of_section K h2 U (overlapObjectSection K)
    (S.X₃.obj.map q.inv.op t)
  have hv : S.g.hom.app _ u = S.X₃.obj.map q.inv.op t := hu
  refine ⟨S.X₂.obj.map q.hom.op u, ?_⟩
  change S.g.hom.app (op W) (S.X₂.obj.map q.hom.op u) = t
  calc
    _ = S.X₃.obj.map q.hom.op (S.g.hom.app _ u) :=
      ConcreteCategory.congr_hom (S.g.hom.naturality q.hom.op) u
    _ = t := by
      rw [hv, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Iso.hom_inv_id,
        op_id, Functor.map_id] <;> rfl

/-- The actual proper nodal curve has nontrivial ordinary small-étale
H¹ with constant Z/2 coefficients whenever 2 is invertible in K. -/
theorem projectiveNode_HOne_nontrivial (h2 : (2 : K) ≠ 0) : Nontrivial (Sheaf.H (F K) 1) := by
  let e : (shortComplex K h2).X₁ ≅ (restriction (affineOpen K) AddCommGrpCat.{0}).obj (F K) :=
    (constantIso K).symm ≪≫ ((restrictionConstantIso (affineOpen K)).app coeff).symm
  exact HOne_nontrivial_of_local_section_lift (affineOpen K) (chartOpen K)
    (chart_ranges_cover K) (F K) (shortComplex K h2) (shortComplex_shortExact K h2)
    e (terminalOne K) (terminal_unlifted K h2) (overlap_lifted K h2)

end
end ManuscriptAudit.NodalProjectiveHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProjectiveHOne.projectiveNode_HOne_nontrivial
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
