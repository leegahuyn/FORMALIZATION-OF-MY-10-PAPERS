import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-!
# The scheme intersection is the pullback in the ambient small étale site
-/

namespace ManuscriptAudit.EtaleOpenIntersection

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleTwoOpenHOne

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k]

private abbrev intersection : X.Etale :=
  Scheme.Etale.mk (pullback.fst j k ≫ j)

private def fstLeg : intersection j k ⟶ Scheme.Etale.mk j :=
  MorphismProperty.Over.homMk (pullback.fst j k) rfl

private def sndLeg : intersection j k ⟶ Scheme.Etale.mk k :=
  MorphismProperty.Over.homMk (pullback.snd j k) (pullback.condition (f := j) (g := k)).symm

private theorem intersection_isPullback :
    IsPullback (fstLeg j k) (sndLeg j k) (openArrow j) (openArrow k) := by
  have h : fstLeg j k ≫ openArrow j = sndLeg j k ≫ openArrow k :=
    MorphismProperty.Over.Hom.ext pullback.condition
  let lift (c : PullbackCone (openArrow j) (openArrow k)) : c.pt ⟶ intersection j k := by
    have hc : c.fst.left ≫ j = c.snd.left ≫ k :=
      congrArg (fun a => a.left) c.condition
    refine MorphismProperty.Over.homMk (pullback.lift c.fst.left c.snd.left hc) ?_
    change pullback.lift c.fst.left c.snd.left hc ≫ (pullback.fst j k ≫ j) = c.pt.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact c.fst.w
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk h lift ?_ ?_ ?_)
  · intro c
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  · intro c
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  · intro c m hm₁ hm₂
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change m.left ≫ pullback.fst j k =
        pullback.lift c.fst.left c.snd.left _ ≫ pullback.fst j k
      rw [pullback.lift_fst]
      exact congrArg (fun a => a.left) hm₁
    · change m.left ≫ pullback.snd j k =
        pullback.lift c.fst.left c.snd.left _ ≫ pullback.snd j k
      rw [pullback.lift_snd]
      exact congrArg (fun a => a.left) hm₂

private abbrev C (S : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj M

/-- Two open schemes with vanishing H¹ and a connected nonempty scheme
intersection give vanishing H¹ for the ambient constant sheaf. -/
theorem ambientHOne_subsingleton (M : AddCommGrpCat.{u})
    (hCover : Set.range j ∪ Set.range k = Set.univ)
    [hConn : PreconnectedSpace (↑(pullback j k) : Type u)]
    [hN : Nonempty (↑(pullback j k) : Type u)]
    (hU : Subsingleton (Sheaf.H (C U M) 1)) (hV : Subsingleton (Sheaf.H (C V M) 1)) :
    Subsingleton (Sheaf.H (C X M) 1) := by
  letI : PreconnectedSpace (intersection j k).left := by
    change PreconnectedSpace (↑(pullback j k) : Type u)
    exact hConn
  letI : Nonempty (intersection j k).left := by
    change Nonempty (↑(pullback j k) : Type u)
    exact hN
  exact constantHOne_subsingleton j k M hCover (fstLeg j k) (sndLeg j k)
    (intersection_isPullback j k) hU hV

end

end ManuscriptAudit.EtaleOpenIntersection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.EtaleOpenIntersection.ambientHOne_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
