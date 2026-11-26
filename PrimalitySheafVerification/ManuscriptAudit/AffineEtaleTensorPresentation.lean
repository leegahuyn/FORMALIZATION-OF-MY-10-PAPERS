import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.LinearAlgebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Tensor presentation of pullbacks on the actual affine étale site

The structure arrow of each affine site object determines its native
base algebra. Pullback of an affine morphism is then represented by
the tensor product, with its canonical two projections.
-/

namespace ManuscriptAudit.AffineEtaleTensorPresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

noncomputable section

universe u

variable (A : Type u) [CommRing A]

abbrev base := Spec (CommRingCat.of A)

abbrev objectRing (U : (base A).AffineEtale) : CommRingCat.{u} :=
  U.left.unop

def structureRingHom (U : (base A).AffineEtale) : CommRingCat.of A ⟶ objectRing A U :=
  let f : Scheme.Spec.obj U.left ⟶ Scheme.Spec.obj (op (CommRingCat.of A)) := U.hom
  (Scheme.Spec.preimage f).unop

theorem spec_structureRingHom (U : (base A).AffineEtale) :
    Spec.map (structureRingHom A U) = U.hom :=
  Scheme.Spec.map_preimage _

theorem objectRingMap_commutes {U V : (base A).AffineEtale} (f : U ⟶ V) :
    structureRingHom A V ≫ f.left.unop = structureRingHom A U := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_structureRingHom, spec_structureRingHom]
  exact f.w

abbrev objectAlgebra (U : (base A).AffineEtale) : Algebra A (objectRing A U) :=
  (structureRingHom A U).hom.toAlgebra

attribute [local instance] objectAlgebra

variable (E : Type u) [CommRing E] [Algebra A E]
variable (U : (base A).AffineEtale)

abbrev tensorRing : Type u := objectRing A U ⊗[A] E

abbrev affineMap : Spec (CommRingCat.of E) ⟶ base A :=
  Spec.map (CommRingCat.ofHom (algebraMap A E))

abbrev tensorScheme := Spec (CommRingCat.of (tensorRing A E U))

def tensorFirst : tensorScheme A E U ⟶ Spec (objectRing A U) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft :
      objectRing A U →ₐ[A] tensorRing A E U).toRingHom))

def tensorSecond : tensorScheme A E U ⟶ Spec (CommRingCat.of E) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : E →ₐ[A] tensorRing A E U).toRingHom))

set_option backward.isDefEq.respectTransparency false in
theorem tensor_isPullback : IsPullback (tensorFirst A E U) (tensorSecond A E U) U.hom (affineMap A E) := by
  rw [← spec_structureRingHom A U]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone A (objectRing A U) E).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit A (objectRing A U) E⟩⟩

def tensorIsoPullback : tensorScheme A E U ≅ pullback U.hom (affineMap A E) :=
  (tensor_isPullback A E U).isoPullback

theorem tensorIsoPullback_inv_fst :
    (tensorIsoPullback A E U).inv ≫ tensorFirst A E U = pullback.fst U.hom (affineMap A E) :=
  (tensor_isPullback A E U).isoPullback_inv_fst

theorem tensorIsoPullback_inv_snd :
    (tensorIsoPullback A E U).inv ≫ tensorSecond A E U = pullback.snd U.hom (affineMap A E) :=
  (tensor_isPullback A E U).isoPullback_inv_snd

end

end ManuscriptAudit.AffineEtaleTensorPresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.AffineEtaleTensorPresentation.spec_structureRingHom,
        ``ManuscriptAudit.AffineEtaleTensorPresentation.objectRingMap_commutes,
        ``ManuscriptAudit.AffineEtaleTensorPresentation.tensor_isPullback,
        ``ManuscriptAudit.AffineEtaleTensorPresentation.tensorIsoPullback_inv_fst,
        ``ManuscriptAudit.AffineEtaleTensorPresentation.tensorIsoPullback_inv_snd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
