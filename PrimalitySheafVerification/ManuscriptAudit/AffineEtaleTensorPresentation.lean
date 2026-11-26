import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.LinearAlgebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

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

theorem tensorIsoPullback_hom_fst :
    (tensorIsoPullback A E U).hom ≫ pullback.fst U.hom (affineMap A E) = tensorFirst A E U :=
  (tensor_isPullback A E U).isoPullback_hom_fst

theorem tensorIsoPullback_hom_snd :
    (tensorIsoPullback A E U).hom ≫ pullback.snd U.hom (affineMap A E) = tensorSecond A E U :=
  (tensor_isPullback A E U).isoPullback_hom_snd

variable {U} {V : (base A).AffineEtale}

def objectAlgHom (f : U ⟶ V) : objectRing A V →ₐ[A] objectRing A U :=
  { f.left.unop.hom with
    commutes' := fun a => congrArg
      (fun k : CommRingCat.of A ⟶ objectRing A U => k.hom a) (objectRingMap_commutes A f) }

def tensorAlgHom (f : U ⟶ V) : tensorRing A E V →ₐ[A] tensorRing A E U :=
  Algebra.TensorProduct.map (objectAlgHom A f) (AlgHom.id A E)

def tensorMap (f : U ⟶ V) : tensorScheme A E U ⟶ tensorScheme A E V :=
  Spec.map (CommRingCat.ofHom (tensorAlgHom A E f).toRingHom)

set_option backward.isDefEq.respectTransparency false in
theorem tensorMap_fst (f : U ⟶ V) :
    tensorMap A E f ≫ tensorFirst A E V =
      tensorFirst A E U ≫ ((Scheme.AffineEtale.Spec (base A)).map f).left := by
  change _ = tensorFirst A E U ≫ Spec.map f.left.unop
  simp only [tensorMap, tensorFirst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change (tensorAlgHom A E f) (b ⊗ₜ[A] (1 : E)) = f.left.unop.hom b ⊗ₜ[A] (1 : E)
  rw [tensorAlgHom, Algebra.TensorProduct.map_tmul] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem tensorMap_snd (f : U ⟶ V) :
    tensorMap A E f ≫ tensorSecond A E V = tensorSecond A E U := by
  simp only [tensorMap, tensorSecond, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change (tensorAlgHom A E f) ((1 : objectRing A V) ⊗ₜ[A] x) =
    (1 : objectRing A U) ⊗ₜ[A] x
  rw [tensorAlgHom, Algebra.TensorProduct.map_tmul, map_one] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem tensorIsoPullback_natural (f : U ⟶ V) :
    tensorMap A E f ≫ (tensorIsoPullback A E V).hom =
      (tensorIsoPullback A E U).hom ≫
        ((SmallEtaleBaseChange.etaleBaseChange (affineMap A E)).map
          ((Scheme.AffineEtale.Spec (base A)).map f)).left := by
  let g := (Scheme.AffineEtale.Spec (base A)).map f
  let f' := ((SmallEtaleBaseChange.etaleBaseChange (affineMap A E)).map g).left
  have hFst : f' ≫ pullback.fst V.hom (affineMap A E) =
      pullback.fst U.hom (affineMap A E) ≫ g.left := by
    simp only [f', SmallEtaleBaseChange.etaleBaseChange,
      MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  have hSnd : f' ≫ pullback.snd V.hom (affineMap A E) =
      pullback.snd U.hom (affineMap A E) := by
    simp only [f', SmallEtaleBaseChange.etaleBaseChange,
      MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
  apply pullback.hom_ext
  · rw [Category.assoc, tensorIsoPullback_hom_fst, Category.assoc, hFst,
      ← Category.assoc, tensorIsoPullback_hom_fst]
    exact tensorMap_fst A E f
  · rw [Category.assoc, tensorIsoPullback_hom_snd, Category.assoc, hSnd,
      tensorIsoPullback_hom_snd]
    exact tensorMap_snd A E f

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
        ``ManuscriptAudit.AffineEtaleTensorPresentation.tensorIsoPullback_inv_snd,
        ``ManuscriptAudit.AffineEtaleTensorPresentation.tensorIsoPullback_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
