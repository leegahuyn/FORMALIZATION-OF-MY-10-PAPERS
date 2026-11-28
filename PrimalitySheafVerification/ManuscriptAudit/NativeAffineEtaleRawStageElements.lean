import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawSections

/-! The raw actual affine section presheaf has actual étale
stage representatives and their equality is witnessed at a stage. -/

namespace ManuscriptAudit.NativeAffineEtaleRawStageElements

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleStageSections (chartArrow etaleObject sectionDiagram)
open NativeAffineEtaleRawSections (rawSectionCocone isColimit_rawSectionCocone rawSection_ι)
open NativeAffineEtaleKanComparison (L affineRestriction raw)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A C)]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

/-- The actual point-map of affine pro-étale charts induced by an algebra map. -/
abbrev chartMap (f : B →ₐ[A] C) :
    ProetaleAffineTensor.object A C ⟶ ProetaleAffineTensor.object A B :=
  MorphismProperty.Over.homMk (specMap A f) (ProetaleAffineTensor.specMap_structureMap A f)

/-- The representative's stage is unchanged and only its map to the chart is composed. -/
abbrev stageAfterMap (f : B →ₐ[A] C) (T : Stage A B) : Stage A C :=
  Stage.of A C (f.comp T.toChart)

set_option maxHeartbeats 2800000 in
/-- Restricting an actual stage representative uses the actual composed chart arrow. -/
theorem rawSection_map (f : B →ₐ[A] C) (T : Stage A B) :
    (rawSectionCocone (B := B) I).ι.app T ≫ (raw (X (A := A)) I).map (chartMap f).op =
      (rawSectionCocone (B := C) I).ι.app (stageAfterMap f T) := by
  let X₀ := X (A := A)
  let P := ((affineRestriction X₀).obj I).obj
  let η := (L X₀).lanUnit.app P
  let U := ((NativeAffineEtaleStageComma.equivalence (A := A) (B := B)).functor.obj T).left
  let F := raw X₀ I
  have h : chartMap f ≫ chartArrow T = chartArrow (stageAfterMap f T) := by
    apply MorphismProperty.Over.Hom.ext
    change specMap A f ≫ specMap A T.toChart = specMap A (f.comp T.toChart)
    rw [← Spec.map_comp] <;> rfl
  rw [rawSection_ι, rawSection_ι]
  change (η.app U ≫ F.map (chartArrow T).op) ≫ F.map (chartMap f).op =
    η.app U ≫ F.map (chartArrow (stageAfterMap f T)).op
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, h]

omit [CommRing C] [Algebra A C] [WeaklyEtale (structureMap A C)] in
/-- Each actual raw section is represented on one actual affine étale stage. -/
theorem exists_representative (s : (raw (X (A := A)) I).obj
    (op (ProetaleAffineTensor.object A B))) :
    ∃ (T : Stage A B) (x : (sectionDiagram (B := B) I).obj T),
      (rawSectionCocone (B := B) I).ι.app T x = s := by
  let h := isColimitOfPreserves (CategoryTheory.forget G.{u}) (isColimit_rawSectionCocone (B := B) I)
  exact Types.jointly_surjective_of_isColimit h s

omit [CommRing C] [Algebra A C] [WeaklyEtale (structureMap A C)] in
/-- Equality of representatives is witnessed by equal restrictions along
two genuine stage maps into a common actual affine étale refinement. -/
theorem exists_equal_representatives (T U : Stage A B)
    (x : (sectionDiagram (B := B) I).obj T) (y : (sectionDiagram (B := B) I).obj U)
    (h : (rawSectionCocone (B := B) I).ι.app T x = (rawSectionCocone (B := B) I).ι.app U y) :
    ∃ (W : Stage A B) (f : T ⟶ W) (g : U ⟶ W),
      (sectionDiagram (B := B) I).map f x = (sectionDiagram (B := B) I).map g y := by
  let hC := isColimitOfPreserves (CategoryTheory.forget G.{u}) (isColimit_rawSectionCocone (B := B) I)
  exact (Types.FilteredColimit.isColimit_eq_iff _ hC).mp h

end
end ManuscriptAudit.NativeAffineEtaleRawStageElements

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleRawStageElements.rawSection_map,
      ``ManuscriptAudit.NativeAffineEtaleRawStageElements.exists_representative,
      ``ManuscriptAudit.NativeAffineEtaleRawStageElements.exists_equal_representatives] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
