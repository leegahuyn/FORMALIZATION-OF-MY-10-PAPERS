import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageRestrictionPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousPullbackNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction

/-! Actual continuous compact-support pullback on a cartesian open square. -/

namespace ManuscriptAudit.ProetaleOpenContinuousPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleDirectImageRestrictionPullback (reindexIso reindexIso_hom_fst
  directImageRestrictionIso directImageRestrictionIso_hom_app_app)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleSchemeCohomologyPullback (continuous mapOfDirectImage)
open OpenProetaleExtension (extensionByZero restriction abelianExtensionByZeroAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X Y V U : Scheme.{0}}
  (f : X ⟶ Y) (g : V ⟶ U) (i : V ⟶ X) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (H : IsPullback i g f j)
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private abbrev D (p : X ⟶ Y) := directImage p A
private abbrev E (p : V ⟶ U) := directImage p A
private abbrev B :
    directImage f A ⋙ restriction j A ≅ restriction i A ⋙ directImage g A :=
  directImageRestrictionIso H

/-- The literal ambient inclusion of extension by zero. -/
def ambient {S T : Scheme.{0}} (l : S ⟶ T) [IsOpenImmersion l] :
    (extensionByZero l A).obj (functions M S) ⟶ functions M T :=
  ((abelianExtensionByZeroAdjunction l).homEquiv _ _).symm (restrictionFunctionsIso l M).inv

set_option maxHeartbeats 6000000 in
private theorem diagonal_restrict :
    (restrictionFunctionsIso j M).inv ≫ (restriction j A).map (diagonal M f) ≫
      (B f g i j H).hom.app (functions M X) =
    diagonal M g ≫ (directImage g A).map (restrictionFunctionsIso i M).inv := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro a
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  change (show C(↥(pullback W.unop.hom g : Scheme.{0}), M) from
    (((B f g i j H).hom.app (functions M X)).hom.app W
      (((restriction j A).map (diagonal M f)).hom.app W
        ((restrictionFunctionsIso j M).inv.hom.app W a))).down) t = _
  have h := directImageRestrictionIso_hom_app_app H (functions M X) W.unop
  have hw : op W.unop = W := rfl
  rw [hw] at h
  rw [h]
  change (show C(↥W.unop.left, M) from a.down)
      ((((reindexIso H).hom.app W.unop).left ≫ pullback.fst (W.unop.hom ≫ j) f) t) =
    (show C(↥W.unop.left, M) from a.down) (pullback.fst W.unop.hom g t)
  rw [reindexIso_hom_fst H W.unop]

/-- The actual map into the direct image of extension by zero, defined by adjunction. -/
def compactToDirectImage :
    (extensionByZero j A).obj (functions M U) ⟶
      (directImage f A).obj ((extensionByZero i A).obj (functions M V)) :=
  let a := abelianExtensionByZeroAdjunction j
  let b := abelianExtensionByZeroAdjunction i
  (a.homEquiv _ _).symm (diagonal M g ≫ (directImage g A).map (b.unit.app (functions M V)) ≫
    (B f g i j H).inv.app ((extensionByZero i A).obj (functions M V)))

set_option maxHeartbeats 7300000 in
/-- Extension by zero pullback commutes with the actual inclusion in ambient coefficients. -/
theorem ambient_commutes :
    compactToDirectImage f g i j H M ≫ (directImage f A).map (ambient M i) =
      ambient M j ≫ diagonal M f := by
  let a := abelianExtensionByZeroAdjunction j
  let b := abelianExtensionByZeroAdjunction i
  let Q := directImage g A
  let R := directImage f A ⋙ restriction j A
  let S := restriction i A ⋙ Q
  let e : R ≅ S := B f g i j H
  let T := (extensionByZero i A).obj (functions M V)
  let z := ambient M i
  let k := (restrictionFunctionsIso j M).inv
  let h := (restrictionFunctionsIso i M).inv
  let v := diagonal M g
  let w := (restriction j A).map (diagonal M f)
  let u := b.unit.app (functions M V)
  apply (a.homEquiv (functions M U) ((directImage f A).obj (functions M X))).injective
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right]
  change (a.homEquiv _ _) ((a.homEquiv _ _).symm (v ≫ Q.map u ≫ e.inv.app T)) ≫ R.map z =
    (a.homEquiv _ _) ((a.homEquiv _ _).symm k) ≫ w
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hu : u ≫ (restriction i A).map z = h := by
    change b.unit.app (functions M V) ≫
      (restriction i A).map ((b.homEquiv (functions M V) (functions M X)).symm h) = h
    exact (b.homEquiv_unit (functions M V) (functions M X)
      ((b.homEquiv (functions M V) (functions M X)).symm h)).symm.trans
        ((b.homEquiv (functions M V) (functions M X)).apply_symm_apply h)
  have hn : e.inv.app T ≫ R.map z = Q.map ((restriction i A).map z) ≫ e.inv.app (functions M X) :=
    (e.inv.naturality z).symm
  apply (cancel_mono (e.hom.app (functions M X))).mp
  calc
    _ = v ≫ Q.map u ≫ (e.inv.app T ≫ R.map z) ≫ e.hom.app (functions M X) := by simp only [Category.assoc]
    _ = v ≫ Q.map h := by
      rw [hn]
      have he : e.inv.app (functions M X) ≫ e.hom.app (functions M X) = 𝟙 _ :=
        (e.app (functions M X)).inv_hom_id
      simp only [Category.assoc, he, Category.comp_id]
      rw [← Q.map_comp, hu]
    _ = _ := (diagonal_restrict f g i j H M).symm.trans (Category.assoc _ _ _).symm

/-- Pullback on actual continuous compact-support cohomology. -/
def compactMap (n : ℕ) :
    Sheaf.H ((extensionByZero j A).obj (functions M U)) n →+
      Sheaf.H ((extensionByZero i A).obj (functions M V)) n :=
  mapOfDirectImage f (compactToDirectImage f g i j H M) n

/-- Forgetting support is compatible with the actual open-square pullback. -/
theorem ambient_naturality (n : ℕ)
    (x : Sheaf.H ((extensionByZero j A).obj (functions M U)) n) :
    Sheaf.H.map (ambient M i) n (compactMap f g i j H M n x) =
      continuous f M n (Sheaf.H.map (ambient M j) n x) :=
  (ProetaleContinuousPullbackNaturality.mapOfDirectImage_natural f (compactToDirectImage f g i j H M)
    (diagonal M f) (ambient M j) (ambient M i) (ambient_commutes f g i j H M).symm n x).symm

end
end ManuscriptAudit.ProetaleOpenContinuousPullback

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleOpenContinuousPullback.ambient_naturality
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
