import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import PrimalitySheafVerification.ManuscriptAudit.AffineProetaleBaseChangeCovers

/-! An equivalence on actual affine pro-étale sites identifies the full
native sheaf categories by the genuine direct image. -/

namespace ManuscriptAudit.AffineProetaleBaseChangeEquivalence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineProetaleSite (inclusion topology baseChange baseChange_comp_inclusion)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Surjective f]

private abbrev G := AddCommGrpCat.{u + 1}
private abbrev J (Z : Scheme.{u}) := Scheme.ProEt.topology Z

/-- The actual affine equivalence is an equivalence of covering sieves. -/
theorem denseSubsite [(baseChange f).IsEquivalence] :
    (baseChange f).IsDenseSubsite (topology Y) (topology X) where
  functorPushforward_mem_iff := AffineProetaleBaseChangeCovers.covering_iff f _

set_option maxHeartbeats 1200000 in
/-- The actual full native direct image is an equivalence if the affine base change is. -/
theorem directImage_isEquivalence [(baseChange f).IsEquivalence] :
    (ProetaleBaseChange.directImage f G.{u}).IsEquivalence := by
  let ix := inclusion X
  let iy := inclusion Y
  let tx := topology X
  let ty := topology Y
  let E := baseChange f
  let B := ProetaleBaseChange.baseChange f
  letI : E.IsDenseSubsite ty tx := denseSubsite f
  letI := Functor.isContinuous_comp E ix ty tx (J X)
  letI := Functor.isContinuous_comp iy B ty (J Y) (J X)
  let px := ix.sheafPushforwardContinuous G.{u} tx (J X)
  let py := iy.sheafPushforwardContinuous G.{u} ty (J Y)
  let pe := E.sheafPushforwardContinuous G.{u} ty tx
  let pf := ProetaleBaseChange.directImage f G.{u}
  letI : px.IsEquivalence := (AffineProetaleSite.sheafEquivalence X).isEquivalence_functor
  letI : py.IsEquivalence := (AffineProetaleSite.sheafEquivalence Y).isEquivalence_functor
  letI : pe.IsEquivalence := inferInstanceAs
    ((baseChange f).sheafPushforwardContinuous G.{u} (topology Y) (topology X)).IsEquivalence
  let e : E ⋙ ix ≅ iy ⋙ B := eqToIso (baseChange_comp_inclusion f)
  let h : px ⋙ pe ≅ pf ⋙ py :=
    Functor.sheafPushforwardContinuousComp (F := E) (G := ix) (A := G.{u})
      (J := ty) (K := tx) (L := J X) ≪≫
    Functor.sheafPushforwardContinuousIso e (A := G.{u}) (J := ty) (K := J X) ≪≫
    (Functor.sheafPushforwardContinuousComp (F := iy) (G := B) (A := G.{u})
      (J := ty) (K := J Y) (L := J X)).symm
  letI : (pf ⋙ py).IsEquivalence := Functor.isEquivalence_of_iso h
  exact Functor.isEquivalence_of_comp_right pf py

/-- The native equivalence has exactly the actual direct-image functor. -/
def directImageEquivalence [(baseChange f).IsEquivalence] :
    Sheaf (J X) G.{u} ≌ Sheaf (J Y) G.{u} :=
  letI := directImage_isEquivalence f
  (ProetaleBaseChange.directImage f G.{u}).asEquivalence

/-- The inverse of this native equivalence carries actual constant sheaves to constants. -/
def inverseConstantIso [(baseChange f).IsEquivalence] :
    constantSheaf (J Y) G.{u} ⋙ (directImageEquivalence f).inverse ≅
      constantSheaf (J X) G.{u} := by
  let e := directImageEquivalence f
  let a := constantSheafAdj (J Y) G.{u} (terminalIsTerminal (C := Y.ProEt))
  let b := constantSheafAdj (J X) G.{u}
    (isLimitOfHasTerminalOfPreservesLimit (ProetaleBaseChange.baseChange f))
  exact (a.comp e.symm.toAdjunction).leftAdjointUniq b

/-- The actual native direct image along the equivalence preserves constants. -/
def directImageConstantIso [(baseChange f).IsEquivalence] :
    constantSheaf (J X) G.{u} ⋙ ProetaleBaseChange.directImage f G.{u} ≅
      constantSheaf (J Y) G.{u} := by
  let e := directImageEquivalence f
  let c := constantSheaf (J Y) G.{u}
  exact (Functor.isoWhiskerRight (inverseConstantIso f) e.functor).symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft c e.counitIso ≪≫ c.rightUnitor

end
end ManuscriptAudit.AffineProetaleBaseChangeEquivalence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineProetaleBaseChangeEquivalence.denseSubsite,
      ``ManuscriptAudit.AffineProetaleBaseChangeEquivalence.directImage_isEquivalence,
      ``ManuscriptAudit.AffineProetaleBaseChangeEquivalence.directImageEquivalence,
      ``ManuscriptAudit.AffineProetaleBaseChangeEquivalence.directImageConstantIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
