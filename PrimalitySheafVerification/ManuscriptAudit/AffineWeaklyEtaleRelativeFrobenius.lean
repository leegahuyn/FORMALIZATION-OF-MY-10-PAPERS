import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleRadicialIso
import PrimalitySheafVerification.ManuscriptAudit.AffineFrobeniusPullback
import PrimalitySheafVerification.ManuscriptAudit.AffineFrobeniusFactorization

/-! Relative Frobenius on an actual affine weakly étale scheme is an
isomorphism, and the absolute Frobenius square is cartesian. -/

namespace ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineAbsoluteFrobenius (frobeniusMap)
open AffineRelativeFrobenius
open AffineFrobeniusFactorization
open RelativeFrobeniusEtale (rightInclusion relativeFrobenius_comp_rightInclusion)
open scoped TensorProduct

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

private abbrev structureMap := Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The relative Frobenius is itself weakly étale, by the cartesian
base change on the tensor target and weakly étale cancellation. -/
theorem relative_weaklyEtale [WeaklyEtale (structureMap A B)] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (relativeFrobenius A B p))) := by
  let T := CommRingCat.of (B ⊗[A] FrobeniusTwist p A)
  let F : CommRingCat.of A ⟶ CommRingCat.of (FrobeniusTwist p A) :=
    CommRingCat.ofHom (algebraMap A (FrobeniusTwist p A))
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let i : CommRingCat.of B ⟶ T := CommRingCat.ofHom (leftInclusion A B p)
  let j : CommRingCat.of (FrobeniusTwist p A) ⟶ T :=
    CommRingCat.ofHom (rightInclusion A B p)
  let r : T ⟶ CommRingCat.of B := CommRingCat.ofHom (relativeFrobenius A B p)
  have hTensor : IsPushout f F i j :=
    CommRingCat.isPushout_tensorProduct A B (FrobeniusTwist p A)
  have hPull : IsPullback (Spec.map i) (Spec.map j) (Spec.map f) (Spec.map F) :=
    AlgebraicGeometry.isPullback_SpecMap_of_isPushout f F i j hTensor
  letI : WeaklyEtale (Spec.map f) := inferInstanceAs (WeaklyEtale (structureMap A B))
  letI : WeaklyEtale (Spec.map j) := by
    rw [← hPull.isoPullback_hom_snd]
    infer_instance
  have hRing : j ≫ r = f :=
    CommRingCat.hom_ext (relativeFrobenius_comp_rightInclusion A B p)
  letI : WeaklyEtale (Spec.map r ≫ Spec.map j) := by
    rw [← Spec.map_comp, hRing]
    infer_instance
  exact WeaklyEtale.of_comp (Spec.map r) (Spec.map j)

/-- The actual affine relative Frobenius of any weakly étale algebra is an isomorphism. -/
theorem relative_isIso [WeaklyEtale (structureMap A B)] : IsIso (Spec.map (CommRingCat.ofHom (relativeFrobenius A B p))) := by
  let f := relativeFrobenius A B p
  let g := leftInclusion A B p
  have hSource (z : B ⊗[A] FrobeniusTwist p A) : g (f z) = z ^ p :=
    (pow_eq_leftInclusion_relativeFrobenius A B p z).symm
  have hTarget (b : B) : f (g b) = b ^ p :=
    DFunLike.congr_fun (relativeFrobenius_comp_leftInclusion A B p) b
  letI : WeaklyEtale (specMap f) := relative_weaklyEtale A B p
  letI : Surjective (specMap f) := specMap_surjective_of_factors_power f p g hSource
  letI : UniversallyInjective (specMap f) :=
    specMap_universallyInjective_of_power_lifts f p (CharP.cast_eq_zero B p)
      (fun b ↦ ⟨g b, hTarget b⟩)
  exact WeaklyEtaleRadicialIso.isIso_of_weaklyEtale_of_universallyInjective (specMap f)

theorem frobenius_square_isPullback [WeaklyEtale (structureMap A B)] :
    IsPullback (frobeniusMap B p) (structureMap A B) (structureMap A B) (frobeniusMap A p) :=
  AffineFrobeniusPullback.frobenius_square_isPullback_of_relative_isIso A B p
    (relative_isIso A B p)

end
end ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius.relative_weaklyEtale,
      ``ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius.relative_isIso,
      ``ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius.frobenius_square_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
