import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Exact limits of abelian groups commute with homology of actual complexes. -/

namespace ManuscriptAudit.ExactLimitComplexHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {J : Type u} [Category.{v} J]

local notation "A" => AddCommGrpCat.{0}
local notation "Ch" => CochainComplex A ℤ
local notation "c" => ComplexShape.up ℤ

/-- Assemble a diagram of complexes as a single complex in the diagram category. -/
def diagramComplex (F : J ⥤ Ch) : CochainComplex (J ⥤ A) ℤ where
  X n := F ⋙ eval A c n
  d i j :=
    { app := fun t ↦ (F.obj t).d i j
      naturality := fun _ _ f ↦ (F.map f).comm i j }
  shape i j h := by
    ext t
    exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by
    ext t
    exact (F.obj t).d_comp_d i j k

private abbrev H (n : ℤ) := homologyFunctor A c n
private abbrev S (F : J ⥤ Ch) (n : ℤ) := (diagramComplex F).sc n

/-- Evaluation identifies the homology of a complex of diagrams with the diagram of homology. -/
def diagramHomologyIso (F : J ⥤ Ch) (n : ℤ) :
    (diagramComplex F).homology n ≅ F ⋙ H n := by
  let E := evaluation J A
  let S₀ := S F n
  let e (t : J) : S₀.homology.obj t ≅ (H n).obj (F.obj t) :=
    (S₀.mapHomologyIso (E.obj t)).symm
  refine NatIso.ofComponents e ?_
  intro s t f
  change S₀.homology.map f ≫ (S₀.mapHomologyIso (E.obj t)).inv =
    (S₀.mapHomologyIso (E.obj s)).inv ≫ ShortComplex.homologyMap (S₀.mapNatTrans (E.map f))
  change (E.map f).app S₀.homology ≫ _ = _
  rw [NatTrans.app_homology (E.map f) S₀]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]

/-- Applying homology to the actual pointwise limit cone gives a limit cone
whenever the shape has exact limits in abelian groups. -/
def isLimitHomologyCone (F : J ⥤ Ch) (n : ℤ) :
    IsLimit ((H n).mapCone (coneOfHasLimitEval F)) := by
  let L : (J ⥤ A) ⥤ A := lim
  letI : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  letI : L.PreservesHomology := inferInstance
  let S₀ := S F n
  let e := diagramHomologyIso F n
  let baseCone := limit.cone S₀.homology
  let hBase : IsLimit ((Cone.postcompose e.hom).obj baseCone) :=
    (IsLimit.postcomposeHomEquiv e baseCone).symm (limit.isLimit S₀.homology)
  let pointComparison : (H n).obj (coneOfHasLimitEval F).pt ≅ limit S₀.homology :=
    S₀.mapHomologyIso L
  apply hBase.ofIsoLimit (Cone.ext pointComparison.symm ?_)
  intro t
  let E := evaluation J A
  change (lim.π t).app S₀.homology ≫ (S₀.mapHomologyIso (E.obj t)).inv =
    (S₀.mapHomologyIso L).inv ≫ ShortComplex.homologyMap (S₀.mapNatTrans (lim.π t))
  rw [NatTrans.app_homology (lim.π t) S₀]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Homology preserves the given native exact-shaped limit of abelian-group complexes. -/
def preservesLimit (F : J ⥤ Ch) (n : ℤ) : PreservesLimit F (H n) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F) (isLimitHomologyCone F n)

end
end ManuscriptAudit.ExactLimitComplexHomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExactLimitComplexHomology.diagramHomologyIso,
      ``ManuscriptAudit.ExactLimitComplexHomology.isLimitHomologyCone,
      ``ManuscriptAudit.ExactLimitComplexHomology.preservesLimit] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
