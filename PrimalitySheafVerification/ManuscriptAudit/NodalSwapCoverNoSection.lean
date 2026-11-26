import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverEtale

/-!
# The finite étale cover of the actual affine node has no section

A section would give a retraction on algebras. After pulling back to the
polynomial normalization it would select one of the two factors.
Both possible values on (t,-t) violate the node's branch condition.
-/

namespace ManuscriptAudit.NodalSwapCoverNoSection

open NodalConductor NodalSwapCover NodalSwapCoverEtale Polynomial
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

noncomputable section

private theorem product_selection {R : Type*} [CommRing R] [IsDomain R]
    (f : R × R →ₐ[R] R) :
    (∀ z, f z = z.1) ∨ (∀ z, f z = z.2) := by
  have hprod : ((1, 0) : R × R) * (0, 1) = 0 := Prod.ext (by simp) (by simp)
  have hadd : ((1, 0) : R × R) + (0, 1) = 1 := Prod.ext (by simp) (by simp)
  have hzero : f (1, 0) * f (0, 1) = 0 := by rw [← map_mul, hprod, map_zero]
  have hone : f (1, 0) + f (0, 1) = 1 := by rw [← map_add, hadd, map_one]
  rcases mul_eq_zero.mp hzero with hL | hR
  · right
    have h : f (0, 1) = 1 := by simpa only [hL, zero_add] using hone
    intro z
    have he : ((0, 1) : R × R) * z = (0, 1) * (z.2, z.2) := Prod.ext (by simp) (by simp)
    have hf := congrArg f he
    simp only [map_mul, h, one_mul] at hf
    exact hf.trans (f.commutes z.2)
  · left
    have h : f (1, 0) = 1 := by simpa only [hR, add_zero] using hone
    intro z
    have he : ((1, 0) : R × R) * z = (1, 0) * (z.1, z.1) := Prod.ext (by simp) (by simp)
    have hf := congrArg f he
    simp only [map_mul, h, one_mul] at hf
    exact hf.trans (f.commutes z.1)

universe u

variable (K : Type u) [Field K]

private abbrev A := coordinates K
private abbrev B := Polynomial K
private abbrev L := Cover K

private def witness : L K :=
  ⟨(X, -X), by
    change (X : K[X]).eval 1 = (-(X : K[X])).eval (-1) ∧
      (X : K[X]).eval (-1) = (-(X : K[X])).eval 1
    simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem no_algebra_retraction (h2 : (2 : K) ≠ 0) : IsEmpty (L K →ₐ[A K] A K) := by
  refine ⟨fun r => ?_⟩
  let e := normalizationRecovery K h2
  let m : (B K ⊗[A K] L K) →ₐ[B K] B K :=
    Algebra.TensorProduct.lift (AlgHom.id (B K) (B K))
      ((Algebra.ofId (A K) (B K)).comp r) (fun _ _ => Commute.all _ _)
  let F : (B K × B K) →ₐ[B K] B K := m.comp e.symm.toAlgHom
  let z := witness K
  have hz : e ((1 : B K) ⊗ₜ[A K] z) = z.val := by
    change normalizationExtension K ((1 : B K) ⊗ₜ[A K] z) = z.val
    rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, map_one, one_mul] <;> rfl
  have hF : F z.val = (r z).val := by
    rw [← hz]
    change m (e.symm (e ((1 : B K) ⊗ₜ[A K] z))) = (r z).val
    rw [e.symm_apply_apply] <;> simp [m, Algebra.TensorProduct.lift_tmul]
  have hR := (mem_equalBranchValues K (r z).val).mp
    (coordinates_le_equalBranchValues K (r z).property)
  rcases product_selection F with hFirst | hSecond
  · have hx : (r z).val = (X : K[X]) := hF.symm.trans (hFirst z.val)
    have h : (1 : K) = -1 := by simpa only [hx, eval_X] using hR
    exact h2 (by linear_combination h)
  · have hx : (r z).val = -(X : K[X]) := hF.symm.trans (hSecond z.val)
    have h : (-1 : K) = 1 := by simpa [hx] using hR
    exact h2 (by linear_combination -h)

abbrev nodeScheme := Spec (CommRingCat.of (A K))
abbrev coverScheme := Spec (CommRingCat.of (L K))

def coverMap : coverScheme K ⟶ nodeScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (A K) (L K)))

theorem coverMap_etale (h2 : (2 : K) ≠ 0) : Etale (coverMap K) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (cover_finite_etale K h2).2)

set_option backward.isDefEq.respectTransparency false in
theorem coverMap_finite (h2 : (2 : K) ≠ 0) : IsFinite (coverMap K) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (A K) (L K))))
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap (A K) (L K)))).2
  change (algebraMap (A K) (L K)).Finite
  exact RingHom.finite_algebraMap.mpr (cover_finite_etale K h2).1

theorem coverMap_surjective (h2 : (2 : K) ≠ 0) : Function.Surjective (coverMap K) :=
  cover_spec_surjective K h2

/-- There is no global section of the native affine scheme morphism. -/
theorem coverMap_has_no_section (h2 : (2 : K) ≠ 0) :
    ¬ ∃ s : nodeScheme K ⟶ coverScheme K, s ≫ coverMap K = 𝟙 (nodeScheme K) := by
  rintro ⟨s, hs⟩
  obtain ⟨r, rfl⟩ := Spec.map_surjective s
  have hr : CommRingCat.ofHom (algebraMap (A K) (L K)) ≫ r = 𝟙 (CommRingCat.of (A K)) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id, coverMap] using hs
  let r' : L K →ₐ[A K] A K :=
    { r.hom with
      commutes' := fun a => congrArg
        (fun f : CommRingCat.of (A K) ⟶ CommRingCat.of (A K) => f.hom a) hr }
  exact (no_algebra_retraction K h2).false r'

abbrev baseObject : (nodeScheme K).Etale := Scheme.Etale.mk (𝟙 (nodeScheme K))

def coverObject (h2 : (2 : K) ≠ 0) : (nodeScheme K).Etale :=
  letI : Etale (coverMap K) := coverMap_etale K h2
  Scheme.Etale.mk (coverMap K)

def coverArrow (h2 : (2 : K) ≠ 0) : coverObject K h2 ⟶ baseObject K :=
  MorphismProperty.Over.homMk (coverMap K) (Category.comp_id _)

theorem coverArrow_mem (h2 : (2 : K) ≠ 0) :
    Sieve.ofArrows (fun _ : Unit => coverObject K h2) (fun _ : Unit => coverArrow K h2) ∈
      (nodeScheme K).smallEtaleTopology (baseObject K) :=
  KummerSiteCover.singleton_mem_smallEtaleTopology (coverArrow K h2) (coverMap_surjective K h2)

end

end ManuscriptAudit.NodalSwapCoverNoSection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverNoSection.no_algebra_retraction,
        ``ManuscriptAudit.NodalSwapCoverNoSection.coverMap_etale,
        ``ManuscriptAudit.NodalSwapCoverNoSection.coverMap_finite,
        ``ManuscriptAudit.NodalSwapCoverNoSection.coverMap_has_no_section,
        ``ManuscriptAudit.NodalSwapCoverNoSection.coverArrow_mem] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
