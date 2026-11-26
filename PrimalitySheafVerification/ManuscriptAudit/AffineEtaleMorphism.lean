import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# Native base change on the affine étale sites

For a morphism of affine schemes, pulling back any affine étale
object remains affine. The actual pullback on the small étale site
therefore lifts to the small affine étale site.
-/

namespace ManuscriptAudit.AffineEtaleMorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- An affine small étale object belongs to the essential image of the affine site. -/
theorem mem_affine_essImage {S : Scheme.{u}} (V : S.Etale) [IsAffine V.left] :
    (Scheme.AffineEtale.Spec S).essImage V := by
  let e : V.left ≅ Spec Γ(V.left, ⊤) := V.left.isoSpec
  let g : Spec Γ(V.left, ⊤) ⟶ S := e.inv ≫ V.hom
  letI : Etale g := by
    change Etale (e.inv ≫ V.hom)
    infer_instance
  let W := Scheme.AffineEtale.mk g
  refine ⟨W, ⟨MorphismProperty.Over.isoMk e.symm ?_⟩⟩
  change e.inv ≫ V.hom = g
  rfl

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

private abbrev native := Scheme.AffineEtale.Spec Y ⋙ SmallEtaleBaseChange.etaleBaseChange f

private theorem native_mem_affine (U : Y.AffineEtale) :
    (Scheme.AffineEtale.Spec X).essImage ((native f).obj U) := by
  let V := (native f).obj U
  letI : IsAffine V.left := by
    change IsAffine (pullback U.hom f)
    exact @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (Spec (unop U.left)) X Y U.hom f inferInstance ‹IsAffine X› ‹IsAffine Y›
  exact mem_affine_essImage V

/-- The actual base change of affine étale objects between affine schemes. -/
def baseChange : Y.AffineEtale ⥤ X.AffineEtale :=
  Functor.essImage.liftFunctor (native f) (Scheme.AffineEtale.Spec X) (native_mem_affine f)

/-- The affine base-change functor realizes the native scheme pullback. -/
def baseChangeSpecIso :
    baseChange f ⋙ Scheme.AffineEtale.Spec X ≅
      Scheme.AffineEtale.Spec Y ⋙ SmallEtaleBaseChange.etaleBaseChange f :=
  Functor.essImage.liftFunctorCompIso (native f) (Scheme.AffineEtale.Spec X) (native_mem_affine f)

end

end ManuscriptAudit.AffineEtaleMorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleMorphism.mem_affine_essImage,
      ``ManuscriptAudit.AffineEtaleMorphism.baseChangeSpecIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
