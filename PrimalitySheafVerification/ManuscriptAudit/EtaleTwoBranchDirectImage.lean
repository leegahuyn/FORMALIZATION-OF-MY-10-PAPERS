import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleDisjointPullbackSections
import PrimalitySheafVerification.ManuscriptAudit.EtaleEpiLocalSurjectivity

/-! Local lifts along two disjoint étale branches glue on the native direct image. -/

namespace ManuscriptAudit.EtaleTwoBranchDirectImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleObjectRestriction EtaleDisjointPullbackSections
open EtaleContinuousDirectImageMaps (baseChangeMap)

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{u}

variable {T Y : Scheme.{u}} (q : Y ⟶ T)
variable {B : Bool → Scheme.{u}} (i : ∀ a, B a ⟶ Y)
variable [∀ a, Etale (i a)] [∀ a, Mono (i a)]
variable (cover : ∀ y : Y, ∃ (a : Bool) (b : B a), i a b = y)
variable (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))

private theorem leg_natural {V W : T.Etale} (g : V ⟶ W) (a : Bool) :
    leg q i V a ≫ (etaleBaseChange q).map g =
      (postcompose (i a)).map ((etaleBaseChange (i a ≫ q)).map g) ≫ leg q i W a := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [leg, baseChangeMap, etaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] <;> rfl
  · simp only [leg, baseChangeMap, etaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc] <;> rfl

private theorem restrict_restrict (F : Y.Etaleᵒᵖ ⥤ A.{u}) {U V W : Y.Etale}
    (g : U ⟶ V) (h : V ⟶ W) (s : F.obj (op W)) :
    F.map g.op (F.map h.op s) = F.map (g ≫ h).op s := by
  rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]

private abbrev branchImage (a : Bool) :=
  restriction (i a) ⋙ directImage (i a ≫ q) A.{u}

set_option maxHeartbeats 2000000 in
/-- If both actual branch images of a sheaf map are epimorphisms, then its full direct image is epi. -/
theorem map_epi_of_branches {F G : Sheaf Y.smallEtaleTopology A.{u}} (α : F ⟶ G)
    (hBranch : ∀ a, Epi ((branchImage q i a).map α)) :
    Epi ((directImage q A.{u}).map α) := by
  classical
  have hLocal : Sheaf.IsLocallySurjective ((directImage q A.{u}).map α) := by
    constructor
    intro W s
    let β (a : Bool) := (branchImage q i a).map α
    let s' (a : Bool) := (sectionsEquiv q i G cover disjoint W s) a
    let R (a : Bool) : Sieve W := Presheaf.imageSieve (β a).hom (s' a)
    have hR (a : Bool) : R a ∈ T.smallEtaleTopology W := by
      letI : Epi (β a) := hBranch a
      letI : Sheaf.IsLocallySurjective (β a) := EtaleEpiLocalSurjectivity.of_epi (β a)
      exact Presheaf.imageSieve_mem T.smallEtaleTopology (β a).hom (U := op W) (s' a)
    refine T.smallEtaleTopology.superset_covering ?_
      (T.smallEtaleTopology.intersection_covering (hR false) (hR true))
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
    change α.hom.app (op ((etaleBaseChange q).obj V)) (eF.symm b) =
      G.obj.map ((etaleBaseChange q).map g).op s
    apply eG.injective
    funext a
    change G.obj.map (leg q i V a).op (α.hom.app _ (eF.symm b)) =
      G.obj.map (leg q i V a).op (G.obj.map ((etaleBaseChange q).map g).op s)
    let h := (postcompose (i a)).map ((etaleBaseChange (i a ≫ q)).map g)
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
end ManuscriptAudit.EtaleTwoBranchDirectImage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleTwoBranchDirectImage.map_epi_of_branches
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
