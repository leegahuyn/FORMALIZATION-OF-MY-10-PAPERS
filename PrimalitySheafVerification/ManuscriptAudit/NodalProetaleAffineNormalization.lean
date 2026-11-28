import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Noetherian
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationDirectImageExact
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageRestrictionPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSurjectiveRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoBranchDirectImage
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleComplement

/-! The actual affine nodal normalization preserves epimorphisms on its
small pro-étale site. Its finite étale swap cover separates its two branches. -/

namespace ManuscriptAudit.NodalProetaleAffineNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalNormalizationFiber (affineLine affineNormalization)
open NodalNormalizationSwapPullback (splitScheme toCover toLine)
open NodalNormalizationDirectImageExact
  (toLine_etale branch branch_over_line branch_mono branches_cover branches_disjoint
    branch_closed branch_split retraction)
open NodalSwapCoverNoSection (coverScheme coverMap coverMap_etale coverMap_surjective)
open NodalConductor (coordinates)
open NodalSwapCover (Cover)
open ProetaleBaseChange (directImage)
open ProetaleObjectRestriction (restriction restrictionAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private theorem branch_open (a : Bool) : IsOpenImmersion (branch K a) := by
  let p := toLine K
  let f := branch K a
  letI : Etale p := toLine_etale K
  let t : affineLine K ⟶ pullback (f ≫ p) p :=
    pullback.lift (𝟙 _) f (Category.id_comp _)
  letI : IsOpenImmersion t := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback f p) inferInstance
  letI : IsIso (f ≫ p) := by
    change IsIso (branch K a ≫ toLine K)
    rw [branch_over_line K a]
    infer_instance
  have ht : t ≫ pullback.snd (f ≫ p) p = f := pullback.lift_snd _ _ _
  rw [← ht]
  infer_instance

private theorem cover_noetherian (h2 : (2 : K) ≠ 0) : NoetherianSpace (coverScheme K) := by
  letI : IsNoetherianRing (coordinates K) := NodalSwapCoverEtale.node_isNoetherian K
  letI : Module.Finite (coordinates K) (Cover K) := (NodalSwapCoverEtale.cover_finite_etale K h2).1
  letI : IsNoetherianRing (Cover K) := Algebra.FiniteType.isNoetherianRing (coordinates K) (Cover K)
  change NoetherianSpace (Spec (CommRingCat.of (Cover K)))
  infer_instance

private abbrev A := AddCommGrpCat.{1}

set_option maxHeartbeats 1800000 in
theorem map_epi (h2 : (2 : K) ≠ 0)
    {F G : Sheaf (Scheme.ProEt.topology (affineLine K)) A} (α : F ⟶ G) [Epi α] :
    Epi ((directImage (affineNormalization K) A).map α) := by
  let f := affineNormalization K
  let j := coverMap K
  let p := toLine K
  let q := toCover K
  letI : Etale j := coverMap_etale K h2
  letI : Etale p := toLine_etale K
  letI : QuasiCompact j := inferInstanceAs (QuasiCompact (coverMap K))
  letI : NoetherianSpace (coverScheme K) := cover_noetherian K h2
  letI : ∀ a, IsOpenImmersion (branch K a) := branch_open K
  letI : ∀ a, Mono (branch K a) := branch_mono K
  letI : (restriction p A).IsLeftAdjoint := (restrictionAdjunction p A).isLeftAdjoint
  let β := (restriction p A).map α
  letI : Epi β := (restriction p A).map_epi α
  have hBranch (a : Bool) :
      Epi ((directImage (branch K a ≫ q) A).map ((restriction (branch K a) A).map β)) := by
    let i := branch K a
    letI : (restriction i A).IsLeftAdjoint := (restrictionAdjunction i A).isLeftAdjoint
    letI : Epi ((restriction i A).map β) := (restriction i A).map_epi β
    letI : IsClosedImmersion (i ≫ q) := branch_closed K h2 a
    exact SplitClosedProetaleComplement.map_epi (i ≫ q) (retraction K a)
      (branch_split K a) ((restriction i A).map β)
  letI : Epi ((directImage q A).map β) :=
    ProetaleTwoBranchDirectImage.map_epi_of_branches q (branch K) (branches_cover K)
      (branches_disjoint K) β hBranch
  let e := ProetaleDirectImageRestrictionPullback.directImageRestrictionIso
    (NodalNormalizationSwapPullback.split_isPullback K h2).flip
  let m := ((directImage f A) ⋙ restriction j A).map α
  have hEpi : Epi m := by
    apply (epi_comp_iff_of_isIso m (e.hom.app G)).mp
    change Epi (((directImage f A ⋙ restriction j A).map α) ≫ e.hom.app G)
    rw [e.hom.naturality α]
    exact inferInstanceAs (Epi (e.hom.app F ≫ (directImage q A).map β))
  letI : Epi ((restriction j A).map ((directImage f A).map α)) := hEpi
  exact ProetaleSurjectiveRestriction.epi_of_restriction_epi j (coverMap_surjective K h2) _

end
end ManuscriptAudit.NodalProetaleAffineNormalization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProetaleAffineNormalization.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
