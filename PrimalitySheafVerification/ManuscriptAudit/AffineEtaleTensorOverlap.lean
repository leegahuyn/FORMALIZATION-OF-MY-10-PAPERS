import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import PrimalitySheafVerification.ManuscriptAudit.UnitCocycleTensor

/-!
# Tensor overlaps in the actual affine étale site

For an affine étale morphism, the double overlap is the spectrum of the
tensor product with its usual two projections. The diagonal and the three
maps from the iterated tensor product are the maps that occur in the
algebraic unit-cocycle law.
-/

namespace ManuscriptAudit.AffineEtaleTensorOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open UnitCocycleTensor

universe u

noncomputable section

private abbrev underlying (X : Scheme.{u}) : X.AffineEtale ⥤ Scheme.{u} :=
  Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙ Over.forget X

set_option backward.isDefEq.respectTransparency false in
private theorem affine_isPullback_of_scheme {X : Scheme.{u}} {P U V W : X.AffineEtale}
    {r₁ : P ⟶ U} {r₂ : P ⟶ V} {f : U ⟶ W} {g : V ⟶ W}
    (h : IsPullback ((underlying X).map r₁) ((underlying X).map r₂)
      ((underlying X).map f) ((underlying X).map g)) :
    IsPullback r₁ r₂ f g := by
  let E := Scheme.AffineEtale.Spec X
  let F := underlying X
  have hw : r₁ ≫ f = r₂ ≫ g := F.map_injective (by simpa only [Functor.map_comp] using h.w)
  refine ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' (PullbackCone.mk r₁ r₂ hw) ?_⟩⟩
  intro s
  have hs : F.map s.fst ≫ F.map f = F.map s.snd ≫ F.map g := by
    simpa only [Functor.map_comp] using F.congr_map s.condition
  let l := h.lift (F.map s.fst) (F.map s.snd) hs
  have h₁ : l ≫ F.map r₁ = F.map s.fst := h.lift_fst _ _ hs
  have h₂ : l ≫ F.map r₂ = F.map s.snd := h.lift_snd _ _ hs
  have hOver : l ≫ P.hom = s.pt.hom := by
    have ha : F.map r₁ ≫ U.hom = P.hom := r₁.w
    have hb : F.map s.fst ≫ U.hom = s.pt.hom := s.fst.w
    rw [← ha, ← Category.assoc, h₁, hb]
  let lo : E.obj s.pt ⟶ E.obj P := MorphismProperty.Over.homMk l hOver
  let m := E.preimage lo
  have hm : F.map m = l := by
    change (Scheme.Etale.forget X ⋙ Over.forget X).map (E.map (E.preimage lo)) = l
    rw [E.map_preimage] <;> rfl
  refine ⟨m, F.map_injective ?_, F.map_injective ?_, ?_⟩
  · rw [Functor.map_comp, hm, h₁]
  · rw [Functor.map_comp, hm, h₂]
  · intro n hn₁ hn₂
    apply F.map_injective
    rw [hm]
    apply h.hom_ext
    · rw [h₁]
      simpa only [Functor.map_comp] using F.congr_map hn₁
    · rw [h₂]
      simpa only [Functor.map_comp] using F.congr_map hn₂

variable (R : Type u) [CommRing R]

/-- The identity object of the actual affine étale site of `Spec R`. -/
def baseObject : (Spec (CommRingCat.of R)).AffineEtale :=
  Scheme.AffineEtale.mk (𝟙 _)

variable {R} {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [Algebra.Etale R A] [Algebra.Etale R B]

variable (R B) in
/-- The object associated with an étale ring algebra. -/
def ofAlgebra : (Spec (CommRingCat.of R)).AffineEtale := by
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R B))
  exact Scheme.AffineEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of affine étale objects induced by an algebra homomorphism. -/
def ofAlgHom (φ : A →ₐ[R] B) : ofAlgebra R B ⟶ ofAlgebra R A :=
  MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom φ.toRingHom).op trivial (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) = Spec.map (CommRingCat.ofHom (algebraMap R B))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x)

variable (R B) in
/-- The structure map from an affine étale algebra to the base object. -/
def coverArrow : ofAlgebra R B ⟶ baseObject R :=
  MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom (algebraMap R B)).op trivial (by
    change Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ 𝟙 _ = _
    exact Category.comp_id _)

variable (R B)

private instance doubleEtale : Algebra.Etale R (B ⊗[R] B) :=
  Algebra.Etale.comp R B (B ⊗[R] B)

private instance tripleEtale : Algebra.Etale R (B ⊗[R] (B ⊗[R] B)) :=
  Algebra.Etale.comp R B (B ⊗[R] (B ⊗[R] B))

/-- The two projections from the tensor double overlap. -/
def firstProjection : ofAlgebra R (B ⊗[R] B) ⟶ ofAlgebra R B :=
  ofAlgHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)

def secondProjection : ofAlgebra R (B ⊗[R] B) ⟶ ofAlgebra R B :=
  ofAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)

/-- The diagonal in the affine overlap is dual to multiplication of tensors. -/
def diagonalArrow : ofAlgebra R B ⟶ ofAlgebra R (B ⊗[R] B) :=
  ofAlgHom ((diagonal R B).restrictScalars R)

/-- The three projections from the triple tensor overlap to the double overlap. -/
def projection12 :
    ofAlgebra R (B ⊗[R] (B ⊗[R] B)) ⟶ ofAlgebra R (B ⊗[R] B) :=
  ofAlgHom ((pull12 R B).restrictScalars R)

def projection13 :
    ofAlgebra R (B ⊗[R] (B ⊗[R] B)) ⟶ ofAlgebra R (B ⊗[R] B) :=
  ofAlgHom ((pull13 R B).restrictScalars R)

def projection23 :
    ofAlgebra R (B ⊗[R] (B ⊗[R] B)) ⟶ ofAlgebra R (B ⊗[R] B) :=
  ofAlgHom (pull23 R B)

set_option backward.isDefEq.respectTransparency false in
/-- The tensor double overlap is a pullback in the actual affine étale site. -/
theorem double_isPullback :
    IsPullback (firstProjection R B) (secondProjection R B) (coverArrow R B) (coverArrow R B) := by
  apply affine_isPullback_of_scheme
  exact Scheme.isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone R B B).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit R B B⟩⟩

end

end ManuscriptAudit.AffineEtaleTensorOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleTensorOverlap.double_isPullback,
      ``ManuscriptAudit.AffineEtaleTensorOverlap.diagonalArrow,
      ``ManuscriptAudit.AffineEtaleTensorOverlap.projection12,
      ``ManuscriptAudit.AffineEtaleTensorOverlap.projection13,
      ``ManuscriptAudit.AffineEtaleTensorOverlap.projection23] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
