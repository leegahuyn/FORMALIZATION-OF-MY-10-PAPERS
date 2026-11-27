import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationFiber
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverConnected
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverNoSection

/-! The affine normalization splits into two closed branches over the native crossed étale cover. -/

namespace ManuscriptAudit.NodalNormalizationSwapPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalNormalizationFiber (A B affineLine affineNormalization)
open NodalSwapCover (Cover)
open NodalSwapCoverConnected (firstProjection secondProjection)
open NodalSwapCoverEtale (normalizationRecovery normalizationExtension)
open NodalSwapCoverNoSection (coverScheme coverMap)
open NodalSwapCoverPatch (polynomialProjection)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

abbrev splitScheme : Scheme.{u} := Spec (CommRingCat.of (B K × B K))

def toCover : splitScheme K ⟶ coverScheme K :=
  Spec.map (CommRingCat.ofHom (polynomialProjection K).toRingHom)

def toLine : splitScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (algebraMap (B K) (B K × B K)))

/-- The ring splitting realizes the actual étale pullback of the normalization. -/
theorem split_isPullback (h2 : (2 : K) ≠ 0) :
    IsPullback (toCover K) (toLine K) (coverMap K) (affineNormalization K) := by
  let T := B K ⊗[A K] Cover K
  let i : CommRingCat.of (B K) ⟶ CommRingCat.of T := CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft : B K →ₐ[A K] T).toRingHom)
  let j : CommRingCat.of (Cover K) ⟶ CommRingCat.of T := CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : Cover K →ₐ[A K] T).toRingHom)
  let r := (normalizationRecovery K h2).toRingEquiv.toCommRingCatIso
  have hTensor : IsPullback (Spec.map j) (Spec.map i) (coverMap K) (affineNormalization K) := by
    apply IsPullback.flip
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct (A K) (B K) (Cover K))
  have hj : j ≫ r.hom = CommRingCat.ofHom (polynomialProjection K).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change normalizationExtension K ((1 : B K) ⊗ₜ[A K] z) = polynomialProjection K z
    rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hi : i ≫ r.hom = CommRingCat.ofHom (algebraMap (B K) (B K × B K)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change normalizationExtension K (z ⊗ₜ[A K] (1 : Cover K)) =
      algebraMap (B K) (B K × B K) z
    rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, map_one, mul_one] <;> rfl
  refine hTensor.of_iso' (Scheme.Spec.mapIso r.op) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change Spec.map r.hom ≫ Spec.map j = toCover K ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, hj] <;> rfl
  · change Spec.map r.hom ≫ Spec.map i = toLine K ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, hi] <;> rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

def first : affineLine K ⟶ splitScheme K :=
  Spec.map (CommRingCat.ofHom (RingHom.fst (B K) (B K)))

def second : affineLine K ⟶ splitScheme K :=
  Spec.map (CommRingCat.ofHom (RingHom.snd (B K) (B K)))

/-- Every point of the split normalization is on one of its disjoint components. -/
theorem components_cover (x : splitScheme K) :
    (∃ y, first K y = x) ∨ (∃ y, second K y = x) := by
  change (∃ y : PrimeSpectrum (B K), PrimeSpectrum.comap (RingHom.fst (B K) (B K)) y = x) ∨
    (∃ y : PrimeSpectrum (B K), PrimeSpectrum.comap (RingHom.snd (B K) (B K)) y = x)
  let e := PrimeSpectrum.primeSpectrumProd (B K) (B K)
  rcases h : e x with y | y
  · left
    exact ⟨y, (PrimeSpectrum.primeSpectrumProd_symm_inl y).symm.trans
      ((congrArg e.symm h.symm).trans (e.symm_apply_apply x))⟩
  · right
    exact ⟨y, (PrimeSpectrum.primeSpectrumProd_symm_inr y).symm.trans
      ((congrArg e.symm h.symm).trans (e.symm_apply_apply x))⟩

/-- The first component maps to the étale cover by the first polynomial projection. -/
theorem first_toCover :
    first K ≫ toCover K = Spec.map (CommRingCat.ofHom (firstProjection K)) := by
  unfold first toCover
  rw [← Spec.map_comp] <;> rfl

/-- The second component maps to the étale cover by the second polynomial projection. -/
theorem second_toCover :
    second K ≫ toCover K = Spec.map (CommRingCat.ofHom (secondProjection K)) := by
  unfold second toCover
  rw [← Spec.map_comp] <;> rfl

theorem first_closed (h2 : (2 : K) ≠ 0) :
    IsClosedImmersion (first K ≫ toCover K) := by
  rw [first_toCover]
  exact IsClosedImmersion.spec_of_surjective _
    (NodalSwapCoverConnected.firstProjection_surjective K h2)

theorem second_closed (h2 : (2 : K) ≠ 0) :
    IsClosedImmersion (second K ≫ toCover K) := by
  rw [second_toCover]
  exact IsClosedImmersion.spec_of_surjective _
    (NodalSwapCoverConnected.secondProjection_surjective K h2)

end

end ManuscriptAudit.NodalNormalizationSwapPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.NodalNormalizationSwapPullback.split_isPullback,
      ``ManuscriptAudit.NodalNormalizationSwapPullback.components_cover,
      ``ManuscriptAudit.NodalNormalizationSwapPullback.first_closed,
      ``ManuscriptAudit.NodalNormalizationSwapPullback.second_closed] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
