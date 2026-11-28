import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRefinementColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCoverDescent
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFixedCoproductGeometry

/-! A surjective base change of a fixed étale model is already
surjective over one genuine affine étale base refinement. -/

namespace ManuscriptAudit.AffineEtaleStageSurjectiveModel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleStageRefinementColimit (refinementDiagram refinementCocone)
open AffineStageFixedCoproductGeometry (left isPullback_cover)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

private theorem surjective_pullback_fst_iff {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback a b f g) :
    Function.Surjective (pullback.fst f g) ↔ Function.Surjective a := by
  let e := h.isoPullback
  have he : e.hom ≫ pullback.fst f g = a := h.isoPullback_hom_fst
  have hi : e.inv ≫ a = pullback.fst f g := calc
    _ = e.inv ≫ e.hom ≫ pullback.fst f g :=
      congrArg (fun m : P ⟶ X ↦ e.inv ≫ m) he.symm
    _ = _ := e.inv_hom_id_assoc _
  constructor
  · intro hs x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨e.inv y, by simpa only [← Scheme.Hom.comp_apply, hi] using hy⟩
  · intro hs x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨e.hom y, by simpa only [← Scheme.Hom.comp_apply, he] using hy⟩

variable (T : Stage A B)
  (E : Type u) [CommRing E] [Algebra T.carrier E] [Algebra.Etale T.carrier E]

private abbrev M := CommRingCat.mkUnder (CommRingCat.of T.carrier) E

set_option maxHeartbeats 4500000 in
/-- The refinement at which the model first covers is an object of
the actual undercategory of base stages. -/
theorem exists_surjective_base (hApprox : FiniteTupleApproximation A B)
    (hCover : Function.Surjective (Spec.map (left (refinementCocone T).pt (M T E)).right)) :
    ∃ U : Under T, Function.Surjective (Spec.map (left ((refinementDiagram T).obj U) (M T E)).right) := by
  have h : Function.Surjective
      (pullback.fst (ProetaleAffineTensor.specMap A T.toChart) (structureMap T.carrier E)) :=
    (surjective_pullback_fst_iff (isPullback_cover (refinementCocone T).pt (M T E))).mpr hCover
  obtain ⟨Q, hQR, hQA, hQE, q, l, hl, hq⟩ :=
    AffineEtaleStageCoverDescent.exists_surjective_refinement (E := E) hApprox T.toChart h
  letI : CommRing Q := hQR
  letI : Algebra A Q := hQA
  letI : Algebra.Etale A Q := hQE
  let Z := Stage.of A B l
  let a : T ⟶ Z := ⟨q, hl⟩
  let U : Under T := Under.mk a
  refine ⟨U, ?_⟩
  exact (surjective_pullback_fst_iff (isPullback_cover ((refinementDiagram T).obj U) (M T E))).mp hq

end
end ManuscriptAudit.AffineEtaleStageSurjectiveModel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageSurjectiveModel.exists_surjective_base
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
