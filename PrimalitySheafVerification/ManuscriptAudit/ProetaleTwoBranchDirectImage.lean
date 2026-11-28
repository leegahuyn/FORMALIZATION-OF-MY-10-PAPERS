import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointPullbackSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-! Local lifts along two disjoint open branches glue on the native direct image. -/

namespace ManuscriptAudit.ProetaleTwoBranchDirectImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange ProetaleObjectRestriction ProetaleDisjointPullbackSections
open OpenProetaleExtension (proetalePostcompose)
open ProetaleContinuousDirectImageMaps (pullbackMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

variable {T Y : Scheme.{0}} (q : Y ⟶ T)
variable {B : Bool → Scheme.{0}} (i : ∀ a, B a ⟶ Y)
variable [∀ a, IsOpenImmersion (i a)] [∀ a, Mono (i a)]
variable (cover : ∀ y : Y, ∃ (a : Bool) (b : B a), i a b = y)
variable (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))

private theorem leg_natural {V W : T.ProEt} (g : V ⟶ W) (a : Bool) :
    leg q i V a ≫ (baseChange q).map g =
      (proetalePostcompose (i a)).map ((baseChange (i a ≫ q)).map g) ≫ leg q i W a := by
  apply MorphismProperty.Over.Hom.ext
  change pullbackMap V.hom (i a) rfl ≫ ((baseChange q).map g).left =
      ((baseChange (i a ≫ q)).map g).left ≫ pullbackMap W.hom (i a) rfl
  apply pullback.hom_ext
  · simp only [pullbackMap, baseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] <;> rfl
  · simp only [pullbackMap, baseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc] <;> rfl

private theorem restrict_restrict (F : Y.ProEtᵒᵖ ⥤ A) {U V W : Y.ProEt}
    (g : U ⟶ V) (h : V ⟶ W) (s : F.obj (op W)) :
    F.map g.op (F.map h.op s) = F.map (g ≫ h).op s := by
  rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]

private abbrev branchImage (a : Bool) :=
  restriction (i a) A ⋙ directImage (i a ≫ q) A

include cover disjoint in
set_option maxHeartbeats 2000000 in
/-- If both actual branch images of a sheaf map are epimorphisms, then its full direct image is epi. -/
theorem map_epi_of_branches {F G : Sheaf (Scheme.ProEt.topology Y) A} (α : F ⟶ G)
    (hBranch : ∀ a, Epi ((branchImage q i a).map α)) :
    Epi ((directImage q A).map α) := by
  classical
  have hLocal : Sheaf.IsLocallySurjective ((directImage q A).map α) := by
    constructor
    intro W s
    let β (a : Bool) := (branchImage q i a).map α
    let s' (a : Bool) := (sectionsEquiv q i G cover disjoint W s) a
    let R (a : Bool) : Sieve W := Presheaf.imageSieve (β a).hom (s' a)
    have hR (a : Bool) : R a ∈ (Scheme.ProEt.topology T) W := by
      letI : Epi (β a) := hBranch a
      letI : Sheaf.IsLocallySurjective (β a) :=
        (Sheaf.isLocallySurjective_iff_epi' A (β a)).mpr inferInstance
      exact Presheaf.imageSieve_mem (Scheme.ProEt.topology T) (β a).hom (U := op W) (s' a)
    refine (Scheme.ProEt.topology T).superset_covering ?_
      ((Scheme.ProEt.topology T).intersection_covering (hR false) (hR true))
    intro V g hg
    have hmem : ∀ a, R a g := by
      intro a
      cases a
      · exact hg.1
      · exact hg.2
    have hLift : ∀ a, ∃ b : F.obj.obj (op (piece q i V a)),
        (β a).hom.app (op V) b = ((branchImage q i a).obj G).obj.map g.op (s' a) := hmem
    choose b hb using hLift
    let eF := sectionsEquiv q i F cover disjoint V
    let eG := sectionsEquiv q i G cover disjoint V
    refine ⟨eF.symm b, ?_⟩
    change α.hom.app (op ((baseChange q).obj V)) (eF.symm b) =
      G.obj.map ((baseChange q).map g).op s
    apply eG.injective
    funext a
    change G.obj.map (leg q i V a).op (α.hom.app _ (eF.symm b)) =
      G.obj.map (leg q i V a).op (G.obj.map ((baseChange q).map g).op s)
    let h := (proetalePostcompose (i a)).map ((baseChange (i a ≫ q)).map g)
    calc
      _ = α.hom.app _ (F.obj.map (leg q i V a).op (eF.symm b)) :=
        (NatTrans.naturality_apply α.hom (leg q i V a).op (eF.symm b)).symm
      _ = α.hom.app (op (piece q i V a)) (b a) :=
        congrArg (α.hom.app (op (piece q i V a))) (congrFun (eF.apply_symm_apply b) a)
      _ = G.obj.map h.op (G.obj.map (leg q i W a).op s) := hb a
      _ = _ := by
        rw [restrict_restrict, restrict_restrict, leg_natural q i g a]
  letI := hLocal
  infer_instance

end
end ManuscriptAudit.ProetaleTwoBranchDirectImage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleTwoBranchDirectImage.map_epi_of_branches
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
