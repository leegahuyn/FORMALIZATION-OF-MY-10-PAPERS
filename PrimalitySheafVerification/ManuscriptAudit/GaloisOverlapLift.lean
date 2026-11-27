import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapEtale

/-! The actual small étale double and triple overlaps accept compatible tuples of arrows. -/

namespace ManuscriptAudit.GaloisTensorSquare

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsGalois K L]

private abbrev X := Spec (CommRingCat.of K)

def pairLift {W : (X K).Etale} (a b : W ⟶ fieldObject K L) :
    W ⟶ pairObject K L :=
  MorphismProperty.Over.homMk
    (pullback.lift a.left b.left ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))
    (by
      change pullback.lift a.left b.left _ ≫ pullback.fst (baseMap K L) (baseMap K L) ≫
        baseMap K L = W.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact MorphismProperty.Over.w a)

@[reassoc, simp] theorem pairLift_first {W : (X K).Etale}
    (a b : W ⟶ fieldObject K L) : pairLift K L a b ≫ pairFirst K L = a :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

@[reassoc, simp] theorem pairLift_second {W : (X K).Etale}
    (a b : W ⟶ fieldObject K L) : pairLift K L a b ≫ pairSecond K L = b :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

theorem pairHom_ext {W : (X K).Etale} {a b : W ⟶ pairObject K L}
    (h₁ : a ≫ pairFirst K L = b ≫ pairFirst K L)
    (h₂ : a ≫ pairSecond K L = b ≫ pairSecond K L) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact congrArg (fun f => f.left) h₁
  · exact congrArg (fun f => f.left) h₂

theorem comp_pairLift {V W : (X K).Etale} (r : V ⟶ W)
    (a b : W ⟶ fieldObject K L) :
    r ≫ pairLift K L a b = pairLift K L (r ≫ a) (r ≫ b) := by
  apply pairHom_ext K L <;> simp [Category.assoc]

def tripleLift {W : (X K).Etale} (a b c : W ⟶ fieldObject K L) :
    W ⟶ tripleObject K L :=
  MorphismProperty.Over.homMk
    (pullback.lift (pairLift K L a b).left (pairLift K L a c).left
      (congrArg (fun f => f.left) ((pairLift_first K L a b).trans (pairLift_first K L a c).symm)))
    (by
      change pullback.lift _ _ _ ≫
        pullback.fst (pairFirst K L).left (pairFirst K L).left ≫
          (pairFirst K L).left ≫ baseMap K L = W.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact MorphismProperty.Over.w (pairLift K L a b))

@[reassoc, simp] theorem tripleLift_firstPair {W : (X K).Etale}
    (a b c : W ⟶ fieldObject K L) :
    tripleLift K L a b c ≫ tripleFirstPair K L = pairLift K L a b :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

@[reassoc, simp] theorem tripleLift_secondPair {W : (X K).Etale}
    (a b c : W ⟶ fieldObject K L) :
    tripleLift K L a b c ≫ tripleSecondPair K L = pairLift K L a c :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

private theorem thirdPair_first :
    tripleThirdPair K L ≫ pairFirst K L = tripleFirstPair K L ≫ pairSecond K L :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

private theorem thirdPair_second :
    tripleThirdPair K L ≫ pairSecond K L = tripleSecondPair K L ≫ pairSecond K L :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

@[reassoc, simp] theorem tripleLift_thirdPair {W : (X K).Etale}
    (a b c : W ⟶ fieldObject K L) :
    tripleLift K L a b c ≫ tripleThirdPair K L = pairLift K L b c := by
  apply pairHom_ext K L
  · rw [Category.assoc, thirdPair_first, ← Category.assoc, tripleLift_firstPair,
      pairLift_second, pairLift_first]
  · rw [Category.assoc, thirdPair_second, ← Category.assoc, tripleLift_secondPair,
      pairLift_second, pairLift_second]

end
end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GaloisTensorSquare.pairLift_first,
      ``ManuscriptAudit.GaloisTensorSquare.pairLift_second,
      ``ManuscriptAudit.GaloisTensorSquare.pairHom_ext,
      ``ManuscriptAudit.GaloisTensorSquare.comp_pairLift,
      ``ManuscriptAudit.GaloisTensorSquare.tripleLift_firstPair,
      ``ManuscriptAudit.GaloisTensorSquare.tripleLift_secondPair,
      ``ManuscriptAudit.GaloisTensorSquare.tripleLift_thirdPair] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
