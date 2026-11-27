import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalArithmeticProjectiveHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartHOneDetection

/-! The actual arithmetic restriction to the smooth locus detects the
coefficient-field class but kills the independent nodal class. -/

namespace ManuscriptAudit.NodalArithmeticSmoothRestriction

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveClosure (projectiveNode)
open NodalProperYChart (chartOpen)
open NodalSmoothLocusOverlap (smoothOpen ySmooth_ambient)
open NodalYChartHOneDetection (smoothObject yIntoSmooth)
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleMayerVietoris (terminalCohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev C := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod 2)
private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology C).obj M

/-- Restriction of the actual ambient étale cohomology presheaf to its smooth open. -/
def restriction :
    (F K).H' 1 (identityObject (projectiveNode K)) →+ (F K).H' 1 (smoothObject K) :=
  (((F K).cohomologyPresheaf 1).map (openArrow (smoothOpen K).ι).op).hom

/-- Over a field with the two arithmetic binary labels, the actual
proper-to-smooth restriction has a two-element kernel and image. -/
theorem kernel_image_card (h2 : (2 : K) ≠ 0)
    (hLine : ZMod 2 ≃+ NodalNormalizationHOneComparison.normalizationHOne K)
    (u : Kˣ) (hu : ¬ ∃ v : Kˣ, v ^ (2 : ℕ) = u) :
    Nat.card (restriction K).ker = 2 ∧ Nat.card (restriction K).range = 2 := by
  obtain ⟨hFin, hc⟩ := NodalArithmeticProjectiveHOne.finite_card_eq_four K h2 hLine u hu
  let e := (terminalCohomologyIso (F K) 1).addCommGroupIsoToAddEquiv
  letI : Finite (NodalArithmeticProjectiveHOne.properHOne K) := hFin
  letI : Finite ((F K).H' 1 (identityObject (projectiveNode K))) := Finite.of_injective e e.injective
  have hCard : Nat.card ((F K).H' 1 (identityObject (projectiveNode K))) = 4 :=
    (Nat.card_congr e.toEquiv).trans hc
  let P := (F K).cohomologyPresheaf 1
  let s := openArrow (smoothOpen K).ι
  let v := yIntoSmooth K
  let y := openArrow (chartOpen K)
  have hA : v ≫ s = y := MorphismProperty.Over.Hom.ext (ySmooth_ambient K)
  have hMap : P.map s.op ≫ P.map v.op = P.map y.op := by
    rw [← P.map_comp, ← op_comp, hA]
  obtain ⟨a, ha, haY⟩ := NodalProjectiveHOne.exists_class_nonzero_affine_zero_y K h2
  obtain ⟨b, hbY⟩ := NodalArithmeticProjectiveHOne.field_class_detected K h2 u hu
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have ha' : restriction K a = 0 := by
    apply NodalYChartHOneDetection.restriction_injective K h2
    change P.map v.op (P.map s.op a) = P.map v.op 0
    rw [map_zero, ← ConcreteCategory.comp_apply, hMap]
    exact haY
  have hb' : restriction K b ≠ 0 := by
    intro hb
    apply hbY
    change P.map y.op b = 0
    change P.map s.op b = 0 at hb
    rw [← hMap, ConcreteCategory.comp_apply, hb, map_zero]
  exact BinaryExactCardinality.card_kernel_range_eq_two (restriction K) a b ha0 ha' hb' hCard

end
end ManuscriptAudit.NodalArithmeticSmoothRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalArithmeticSmoothRestriction.kernel_image_card
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
