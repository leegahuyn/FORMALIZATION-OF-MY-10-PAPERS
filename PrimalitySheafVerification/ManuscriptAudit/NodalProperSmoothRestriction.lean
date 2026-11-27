import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneExact
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartHOneDetection

/-! The actual restriction from the proper nodal curve to its genuine
smooth locus kills all geometric mod-two degree-one classes. -/

namespace ManuscriptAudit.NodalProperSmoothRestriction

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveClosure (affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalSmoothLocusOverlap (smoothOpen smoothScheme ySmooth_ambient)
open NodalProjectiveHOneExact (projectiveHOne projectiveHOneEquiv)
open NodalYChartHOneDetection (smoothObject yIntoSmooth)
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleMayerVietoris (terminalCohomologyIso)
open OpenEtaleExtension (openCohomologyPresheafEquiv restrictionConstantIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev C := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod 2)
private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology C).obj M
private abbrev presheaf := (F K).cohomologyPresheaf 1

private theorem binary_cases (x : ZMod 2) : x = 0 ∨ x = 1 :=
  (show ∀ y : ZMod 2, y = 0 ∨ y = 1 by decide) x

/-- On the actual ambient étale cohomology presheaf, restriction to the
smooth locus is zero in degree one. -/
theorem presheaf_restriction_eq_zero (h2 : (2 : K) ≠ 0) :
    (presheaf K).map (openArrow (smoothOpen K).ι).op = 0 := by
  let s := (smoothOpen K).ι
  let P := presheaf K
  let r := openArrow s
  let y := yIntoSmooth K
  let rY := openArrow (chartOpen K)
  have hArrow : y ≫ r = rY := by
    apply MorphismProperty.Over.Hom.ext
    exact ySmooth_ambient K
  have hMap : P.map r.op ≫ P.map y.op = P.map rY.op := by
    rw [← P.map_comp, ← op_comp, hArrow]
  obtain ⟨a, ha, haY⟩ := NodalProjectiveHOne.exists_class_nonzero_affine_zero_y K h2
  let e := ((terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv).trans (projectiveHOneEquiv K h2)
  have hA : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have ea : e a = 1 := (binary_cases (e a)).resolve_left
    (fun h => hA (e.injective (h.trans (map_zero e).symm)))
  apply AddCommGrpCat.ext
  intro x
  change P.map r.op x = 0
  apply NodalYChartHOneDetection.restriction_injective K h2
  change P.map y.op (P.map r.op x) = P.map y.op 0
  rw [map_zero, ← ConcreteCategory.comp_apply, hMap]
  rcases binary_cases (e x) with h | h
  · have hx : x = 0 := e.injective (h.trans (map_zero e).symm)
    rw [hx, map_zero]
  · have hx : x = a := e.injective (h.trans ea.symm)
    rw [hx]
    exact haY

private abbrev smoothHOne :=
  Sheaf.H ((constantSheaf (smoothScheme K).smallEtaleTopology C).obj M) 1

/-- The ordinary cohomology restriction realized by the ambient presheaf. -/
def restriction : projectiveHOne K →+ smoothHOne K := by
  let s := (smoothOpen K).ι
  let e₀ := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv s (F K) 1
  let e₂ := ((Sheaf.functorH (smoothScheme K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso s).app M)).addCommGroupIsoToAddEquiv
  exact (e₁.trans e₂).toAddMonoidHom.comp
    (((presheaf K).map (openArrow s).op).hom.comp e₀.symm.toAddMonoidHom)

/-- Both groups have one binary generator, and the actual geometric
restriction map between them is zero. -/
theorem restriction_eq_zero (h2 : (2 : K) ≠ 0) : restriction K = 0 := by
  let s := (smoothOpen K).ι
  let e₀ := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  let e₁ := openCohomologyPresheafEquiv s (F K) 1
  let e₂ := ((Sheaf.functorH (smoothScheme K).smallEtaleTopology 1).mapIso
    ((restrictionConstantIso s).app M)).addCommGroupIsoToAddEquiv
  ext x
  change (e₁.trans e₂) ((presheaf K).map (openArrow s).op (e₀.symm x)) = 0
  rw [presheaf_restriction_eq_zero K h2] <;> exact map_zero _

end
end ManuscriptAudit.NodalProperSmoothRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProperSmoothRestriction.presheaf_restriction_eq_zero,
      ``ManuscriptAudit.NodalProperSmoothRestriction.restriction_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
