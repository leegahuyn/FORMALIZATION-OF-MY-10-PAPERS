import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import PrimalitySheafVerification.ManuscriptAudit.NativeEtaleSingletonSectionGluing

/-! Once the finite étale data are descended, gluing on a genuine
affine étale stage gives gluing for the raw native sections. -/

namespace ManuscriptAudit.NativeAffineEtaleRawGluingAtStage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleStageSections (etaleObject etaleMap sectionDiagram)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (chartMap stageAfterMap rawSection_map)
open NativeAffineEtaleKanComparison (raw)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})
  (k : B →ₐ[A] D) (T : Stage A B) (U : Stage A D) (a : stageAfterMap k T ⟶ U)

private abbrev f := etaleMap a

set_option maxHeartbeats 3500000 in
/-- A matching section on an actual finite cover model is glued by
the actual étale sheaf and gives a preimage in the raw chart sections. -/
theorem exists_raw_section (hCov : Function.Surjective (f k T U a).left)
    (x : (sectionDiagram (B := D) I).obj U)
    (hMatch : I.obj.map (pullback.fst (f k T U a) (f k T U a)).op x =
      I.obj.map (pullback.snd (f k T U a) (f k T U a)).op x) :
    ∃ y : (raw (X (A := A)) I).obj (op (ProetaleAffineTensor.object A B)),
      (raw (X (A := A)) I).map (chartMap k).op y = (rawSectionCocone (B := D) I).ι.app U x := by
  let u := f k T U a
  obtain ⟨y, hy, _⟩ := NativeEtaleSingletonSectionGluing.existsUnique_glue I u
    (pullback.fst u u) (pullback.snd u u) (IsPullback.of_hasPullback u u) hCov x hMatch
  change (sectionDiagram (B := D) I).map a y = x at hy
  refine ⟨(rawSectionCocone (B := B) I).ι.app T y, ?_⟩
  have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I k T)) y
  change (raw (X (A := A)) I).map (chartMap k).op ((rawSectionCocone (B := B) I).ι.app T y) =
    (rawSectionCocone (B := D) I).ι.app (stageAfterMap k T) y at h
  rw [h, ← hy]
  exact (DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    ((rawSectionCocone (B := D) I).w a)) y).symm

set_option maxHeartbeats 3100000 in
/-- Equality after an actual covering stage restriction is detected
by the separatedness of the actual étale sheaf. -/
theorem raw_eq_of_cover_restriction (hCov : Function.Surjective (f k T U a).left)
    (x y : (sectionDiagram (B := B) I).obj T)
    (he : I.obj.map (f k T U a).op x = I.obj.map (f k T U a).op y) :
    (rawSectionCocone (B := B) I).ι.app T x = (rawSectionCocone (B := B) I).ι.app T y := by
  let u := f k T U a
  let p := pullback.fst u u
  let q := pullback.snd u u
  let z := I.obj.map u.op x
  have hz : I.obj.map p.op z = I.obj.map q.op z := by
    change I.obj.map p.op (I.obj.map u.op x) = I.obj.map q.op (I.obj.map u.op x)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun g : pullback u u ⟶ etaleObject T ↦ I.obj.map g.op x)
      (pullback.condition (f := u) (g := u))
  obtain ⟨w, _, hW⟩ := NativeEtaleSingletonSectionGluing.existsUnique_glue I u p q
    (IsPullback.of_hasPullback u u) hCov z hz
  have hxy : x = y := (hW x rfl).trans (hW y he.symm).symm
  rw [hxy]

end
end ManuscriptAudit.NativeAffineEtaleRawGluingAtStage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleRawGluingAtStage.exists_raw_section,
      ``ManuscriptAudit.NativeAffineEtaleRawGluingAtStage.raw_eq_of_cover_restriction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
