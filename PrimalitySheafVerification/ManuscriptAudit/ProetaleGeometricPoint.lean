import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleGeometricCoverLift

/-! An actual map from an algebraically closed field defines a point of
the native pro-étale site in its cohomology universe. -/

namespace ManuscriptAudit.ProetaleGeometricPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
variable (s : Spec (CommRingCat.of K) ⟶ S)

/-- The actual fiber of pro-étale objects over the geometric field map. -/
abbrev fiber : S.ProEt ⥤ Type (u + 1) :=
  Scheme.ProEt.forget S ⋙ coyoneda.obj (op (Over.mk s)) ⋙ uliftFunctor.{u + 1}

set_option maxHeartbeats 900000 in
/-- The native pro-étale point associated with an algebraically closed geometric point. -/
def point : (Scheme.ProEt.topology S).Point.{u + 1} where
  fiber := fiber s
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := by
    let E := (fiber s).Elements
    letI : EssentiallySmall.{u + 1} E := EssentiallySmall.mk' (AsSmall.equiv : E ≌ AsSmall.{0} E)
    exact initiallySmall_of_essentiallySmall E
  jointly_surjective {U} R hR z := by
    let q : Over.mk s ⟶ (Scheme.ProEt.forget S).obj U := z.down
    obtain ⟨a, ha, hq⟩ := Over.homMk_surjective q
    obtain ⟨V, f, hf, b, hb⟩ := ProetaleGeometricCoverLift.exists_lift K R hR a
    have hw : b ≫ V.hom = s := by
      rw [← MorphismProperty.Over.w f, ← Category.assoc, hb]
      exact ha
    let p : Over.mk s ⟶ (Scheme.ProEt.forget S).obj V := Over.homMk b hw
    refine ⟨V, f, hf, ULift.up p, ?_⟩
    apply ULift.ext
    change p ≫ (Scheme.ProEt.forget S).map f = q
    rw [hq]
    apply Over.OverMorphism.ext
    exact hb

end
end ManuscriptAudit.ProetaleGeometricPoint

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleGeometricPoint.point
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
