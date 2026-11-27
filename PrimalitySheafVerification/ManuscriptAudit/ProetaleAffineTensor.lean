import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.LinearAlgebra
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! Affine tensor products represent actual fibre products of weakly
étale affine charts in the native pro-étale site. -/

namespace ManuscriptAudit.ProetaleAffineTensor

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [CommRing A]

abbrev spectrum (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

abbrev structureMap (R : Type u) [CommRing R] [Algebra A R] : spectrum R ⟶ spectrum A :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

abbrev specMap {R T : Type u} [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
    (g : R →ₐ[A] T) : spectrum T ⟶ spectrum R :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

@[reassoc]
theorem specMap_structureMap {R T : Type u} [CommRing R] [CommRing T] [Algebra A R]
    [Algebra A T] (g : R →ₐ[A] T) :
    specMap A g ≫ structureMap A R = structureMap A T := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext g.commutes)

abbrev terminal : (spectrum A).ProEt := Scheme.ProEt.mk (𝟙 (spectrum A))

abbrev object (R : Type u) [CommRing R] [Algebra A R] [WeaklyEtale (structureMap A R)] :
    (spectrum A).ProEt :=
  Scheme.ProEt.mk (structureMap A R)

/-- An algebra map, contravariantly, on the small pro-étale site of the base. -/
def arrow {R T : Type u} [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
    [WeaklyEtale (structureMap A R)] [WeaklyEtale (structureMap A T)]
    (g : R →ₐ[A] T) : object A T ⟶ object A R :=
  MorphismProperty.Over.homMk (specMap A g) (specMap_structureMap A g)

/-- The structure arrow to the terminal site object. -/
def toTerminal (R : Type u) [CommRing R] [Algebra A R] [WeaklyEtale (structureMap A R)] :
    object A R ⟶ terminal A :=
  MorphismProperty.Over.homMk (structureMap A R) (Category.comp_id _)

theorem underlying_isPullback {S : Scheme.{u}} {P U V T : S.ProEt}
    {a : P ⟶ U} {b : P ⟶ V} {f : U ⟶ T} {g : V ⟶ T}
    (h : IsPullback a.left b.left f.left g.left) : IsPullback a b f g := by
  refine IsPullback.mk' (MorphismProperty.Over.Hom.ext h.w) ?_ ?_
  · intro W i j h₁ h₂
    apply MorphismProperty.Over.Hom.ext
    exact h.hom_ext (congrArg (fun k : W ⟶ U ↦ k.left) h₁)
      (congrArg (fun k : W ⟶ V ↦ k.left) h₂)
  · intro W i j hij
    have hc := congrArg (fun k : W ⟶ T ↦ k.left) hij
    let l := h.lift i.left j.left hc
    have hw : l ≫ P.hom = W.hom := by
      rw [← a.w, ← Category.assoc, show l ≫ a.left = i.left from h.lift_fst _ _ _]
      exact i.w
    refine ⟨MorphismProperty.Over.homMk l hw, MorphismProperty.Over.Hom.ext (h.lift_fst _ _ _),
      MorphismProperty.Over.Hom.ext (h.lift_snd _ _ _)⟩

variable (R T : Type u) [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]

abbrev leftInclusion : R →ₐ[A] R ⊗[A] T := Algebra.TensorProduct.includeLeft
abbrev rightInclusion : T →ₐ[A] R ⊗[A] T := Algebra.TensorProduct.includeRight

theorem specTensor_isPullback :
    IsPullback (specMap A (leftInclusion A R T)) (specMap A (rightInclusion A R T))
      (structureMap A R) (structureMap A T) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A R T)

instance tensor_weaklyEtale [WeaklyEtale (structureMap A R)] [WeaklyEtale (structureMap A T)] :
    WeaklyEtale (structureMap A (R ⊗[A] T)) := by
  let i := specMap A (leftInclusion A R T)
  haveI : WeaklyEtale i := MorphismProperty.of_isPullback (P := @WeaklyEtale)
    (specTensor_isPullback A R T).flip (inferInstanceAs (WeaklyEtale (structureMap A T)))
  rw [← specMap_structureMap A (leftInclusion A R T)]
  change WeaklyEtale (i ≫ structureMap A R)
  infer_instance

variable [WeaklyEtale (structureMap A R)] [WeaklyEtale (structureMap A T)]

/-- Tensor spectra give the actual fibre product of the affine site objects. -/
theorem tensor_isPullback :
    IsPullback (arrow A (leftInclusion A R T)) (arrow A (rightInclusion A R T))
      (toTerminal A R) (toTerminal A T) :=
  underlying_isPullback (specTensor_isPullback A R T)

end
end ManuscriptAudit.ProetaleAffineTensor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineTensor.underlying_isPullback,
      ``ManuscriptAudit.ProetaleAffineTensor.tensor_weaklyEtale,
      ``ManuscriptAudit.ProetaleAffineTensor.tensor_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
