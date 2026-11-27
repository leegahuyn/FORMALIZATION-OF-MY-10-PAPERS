import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerDifference

/-! Actual section complexes of injective sheaf resolutions and actual lifted transitions. -/

namespace ManuscriptAudit.SheafSectionResolutionComplex

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}
local notation "S" => Sheaf J A
private abbrev Ch := CochainComplex A ℤ

variable [HasSheafify J A]

/-- Actual evaluation of an abelian sheaf at the specified site object. -/
abbrev sections (T : C) : S ⥤ A := (sheafSections J A).obj (op T)

instance sections_additive (T : C) : (sections J T).Additive :=
  ⟨by intros; rfl⟩

variable [inj : EnoughInjectives (Sheaf J A)]

include inj

/-- The chosen injective resolution of the actual coefficient sheaf. -/
abbrev resolution (F : S) : InjectiveResolution F := by
  letI : EnoughInjectives S := inj
  exact InjectiveResolution.of F

/-- The actual integer-indexed sections complex on the chosen injective resolution. -/
def sectionComplex (T : C) (F : S) : Ch :=
  ((sections J T).mapHomologicalComplex (ComplexShape.up ℤ)).obj (resolution J F).cochainComplex

/-- Lift a sheaf map to the chosen injective resolutions using their native comparison maps. -/
def resolutionMap {F G : S} (f : F ⟶ G) :
    InjectiveResolution.Hom (resolution J F) (resolution J G) f where
  hom := InjectiveResolution.desc f (resolution J G) (resolution J F)
  ι_f_zero_comp_hom_f_zero := by
    simpa using InjectiveResolution.desc_commutes_zero f (resolution J G) (resolution J F)

/-- The section complex arrow induced by the displayed lift of a coefficient map. -/
def sectionComplexMap (T : C) {F G : S} (f : F ⟶ G) :
    sectionComplex J T F ⟶ sectionComplex J T G :=
  ((sections J T).mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionMap J f).hom'

/-- Actual mapping-cocone model of countable compatible derived sections for a coefficient tower. -/
def sectionsTowerFiber (T : C) (F : ℕ → S) (transition : ∀ r, F (r + 1) ⟶ F r) : Ch :=
  ComplexTowerDifference.mappingFiber (fun r ↦ sectionComplex J T (F r))
    (fun r ↦ sectionComplexMap J T (transition r))

end
end ManuscriptAudit.SheafSectionResolutionComplex

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafSectionResolutionComplex.sectionComplex,
      ``ManuscriptAudit.SheafSectionResolutionComplex.resolutionMap,
      ``ManuscriptAudit.SheafSectionResolutionComplex.sectionComplexMap,
      ``ManuscriptAudit.SheafSectionResolutionComplex.sectionsTowerFiber] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
