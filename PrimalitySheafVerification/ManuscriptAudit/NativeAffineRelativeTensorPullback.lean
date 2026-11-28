import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! The native self-intersection of an affine chart over another
affine chart is the literal relative tensor spectrum. -/

namespace ManuscriptAudit.NativeAffineRelativeTensorPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)
open NativeAffineEtaleRawStageElements (chartMap stageAfterMap rawSection_map
  exists_representative exists_equal_representatives)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleStageSections (sectionDiagram)
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleKanComparison (raw)
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)] [WeaklyEtale (structureMap B D)]

abbrev relativeMap := IsScalarTower.toAlgHom A B D
abbrev left := (includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars A
abbrev right := (includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars A

instance tensor_weaklyEtale : WeaklyEtale (structureMap A (D ⊗[B] D)) := by
  let h := ProetaleAffineTensor.specTensor_isPullback B D D
  letI : WeaklyEtale (specMap A (left (A := A) (B := B) (D := D))) :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) h.flip
      (inferInstanceAs (WeaklyEtale (structureMap B D)))
  rw [← ProetaleAffineTensor.specMap_structureMap A (left (A := A) (B := B) (D := D))]
  infer_instance

/-- Actual affine weakly étale fibre product, including both face maps. -/
theorem isPullback :
    IsPullback (chartMap (left (A := A) (B := B) (D := D)))
      (chartMap (right (A := A) (B := B) (D := D)))
      (chartMap (relativeMap (A := A) (B := B) (D := D)))
      (chartMap (relativeMap (A := A) (B := B) (D := D))) :=
  ProetaleAffineTensor.underlying_isPullback (ProetaleAffineTensor.specTensor_isPullback B D D)

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}
private abbrev k := chartMap (relativeMap (A := A) (B := B) (D := D))

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev P := raw (X (A := A)) I

private theorem map_map {U V W : (X (A := A)).ProEt} (f : U ⟶ V) (g : V ⟶ W)
    (x : (P I).obj (op W)) :
    (P I).map f.op ((P I).map g.op x) = (P I).map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 4500000 in
/-- A literal raw matching section yields one absolute étale
representative and one actual finite witness to its matching equation. -/
theorem exists_matching_representatives
    (x : (P I).obj (op (ProetaleAffineTensor.object A D)))
    (hx : (P I).map (pullback.fst (k (A := A) (B := B) (D := D))
        (k (A := A) (B := B) (D := D))).op x =
      (P I).map (pullback.snd (k (A := A) (B := B) (D := D))
        (k (A := A) (B := B) (D := D))).op x) :
    ∃ (M : Stage A D) (z : (sectionDiagram (B := D) I).obj M)
      (N : Stage A (D ⊗[B] D))
      (p : stageAfterMap (left (A := A) (B := B) (D := D)) M ⟶ N)
      (q : stageAfterMap (right (A := A) (B := B) (D := D)) M ⟶ N),
      (rawSectionCocone (B := D) I).ι.app M z = x ∧
        (sectionDiagram (B := D ⊗[B] D) I).map p z =
          (sectionDiagram (B := D ⊗[B] D) I).map q z := by
  let l := left (A := A) (B := B) (D := D)
  let r := right (A := A) (B := B) (D := D)
  have hPB := isPullback (A := A) (B := B) (D := D)
  have hm : (P I).map (chartMap l).op x = (P I).map (chartMap r).op x := by
    rw [← hPB.isoPullback_hom_fst, ← hPB.isoPullback_hom_snd, ← map_map, ← map_map, hx]
  obtain ⟨M, z, hz⟩ := exists_representative I x
  have hl := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I l M)) z
  have hr := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I r M)) z
  change (P I).map (chartMap l).op ((rawSectionCocone (B := D) I).ι.app M z) =
    (rawSectionCocone (B := D ⊗[B] D) I).ι.app (stageAfterMap l M) z at hl
  change (P I).map (chartMap r).op ((rawSectionCocone (B := D) I).ι.app M z) =
    (rawSectionCocone (B := D ⊗[B] D) I).ι.app (stageAfterMap r M) z at hr
  rw [hz] at hl hr
  obtain ⟨N, p, q, hpq⟩ := exists_equal_representatives I
    (stageAfterMap l M) (stageAfterMap r M) z z (hl.symm.trans (hm.trans hr))
  exact ⟨M, z, N, p, q, hz, hpq⟩

end
end ManuscriptAudit.NativeAffineRelativeTensorPullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRelativeTensorPullback.exists_matching_representatives
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
