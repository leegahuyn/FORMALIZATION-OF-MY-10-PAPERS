import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks
import PrimalitySheafVerification.ManuscriptAudit.AffineAbsoluteFrobenius
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRelativeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.RelativeFrobeniusEtale

/-!
# The absolute Frobenius square of an affine étale morphism

The Frobenius base change is the spectrum of the twisted tensor
product. The relative Frobenius identifies its pullback apex with
the source scheme.
-/

namespace ManuscriptAudit.AffineFrobeniusPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ManuscriptAudit.AffineAbsoluteFrobenius
open ManuscriptAudit.AffineRelativeFrobenius
open ManuscriptAudit.RelativeFrobeniusEtale
open scoped TensorProduct

universe u

noncomputable section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- If the relative map is an isomorphism, the square of absolute Frobenius maps is a pullback. -/
theorem frobenius_square_isPullback_of_relative_isIso
    (h : IsIso (Spec.map (CommRingCat.ofHom (relativeFrobenius A B p)))) :
    IsPullback (frobeniusMap B p) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) (frobeniusMap A p) := by
  let T := CommRingCat.of (B ⊗[A] FrobeniusTwist p A)
  let F : CommRingCat.of A ⟶ CommRingCat.of (FrobeniusTwist p A) :=
    CommRingCat.ofHom (algebraMap A (FrobeniusTwist p A))
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let i : CommRingCat.of B ⟶ T := CommRingCat.ofHom (leftInclusion A B p)
  let j : CommRingCat.of (FrobeniusTwist p A) ⟶ T :=
    CommRingCat.ofHom (rightInclusion A B p)
  let r : T ⟶ CommRingCat.of B := CommRingCat.ofHom (relativeFrobenius A B p)
  letI : IsIso (Spec.map r) := h
  have hTensor : IsPushout f F i j :=
    CommRingCat.isPushout_tensorProduct A B (FrobeniusTwist p A)
  have hPull : IsPullback (Spec.map i) (Spec.map j) (Spec.map f) (Spec.map F) :=
    AlgebraicGeometry.isPullback_SpecMap_of_isPushout f F i j hTensor
  have hi : i ≫ r = CommRingCat.ofHom (frobenius B p) :=
    CommRingCat.hom_ext (relativeFrobenius_comp_leftInclusion A B p)
  have hj : j ≫ r = f :=
    CommRingCat.hom_ext (relativeFrobenius_comp_rightInclusion A B p)
  have hF : F = CommRingCat.ofHom (frobenius A p) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change algebraMap A A (frobenius A p a) = frobenius A p a
    exact Algebra.algebraMap_self_apply _
  refine hPull.of_iso' (asIso (Spec.map r)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map r ≫ Spec.map i =
      Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, hi]
  · change Spec.map r ≫ Spec.map j = Spec.map f ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, hj]
  · change 𝟙 _ ≫ Spec.map f = Spec.map f ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · change 𝟙 _ ≫ Spec.map F =
      Spec.map (CommRingCat.ofHom (frobenius A p)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, hF]

/-- The actual square of absolute Frobenius maps is cartesian for an affine étale morphism. -/
theorem frobenius_square_isPullback [Algebra.Etale A B] :
    IsPullback (frobeniusMap B p) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) (frobeniusMap A p) :=
  frobenius_square_isPullback_of_relative_isIso A B p
    (AffineEtaleRelativeFrobenius.spec_relativeFrobenius_isIso A B p)

end

end ManuscriptAudit.AffineFrobeniusPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AffineFrobeniusPullback.frobenius_square_isPullback_of_relative_isIso,
      ``ManuscriptAudit.AffineFrobeniusPullback.frobenius_square_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
