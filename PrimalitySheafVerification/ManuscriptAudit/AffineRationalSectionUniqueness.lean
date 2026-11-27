import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.AffineScheme

/-! A rational section of an affine scheme over a field is determined
by the point that it meets. -/

namespace ManuscriptAudit.AffineRationalSectionUniqueness

open AlgebraicGeometry CategoryTheory

universe u

variable {K : Type u} [Field K] {R : CommRingCat.{u}}

theorem section_eq_of_point_eq
    (f : Spec R ⟶ Spec (CommRingCat.of K))
    (s t : Spec (CommRingCat.of K) ⟶ Spec R)
    (hs : s ≫ f = 𝟙 _) (ht : t ≫ f = 𝟙 _)
    (h : s (IsLocalRing.closedPoint K) = t (IsLocalRing.closedPoint K)) : s = t := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨α, rfl⟩ := Spec.map_surjective s
  obtain ⟨β, rfl⟩ := Spec.map_surjective t
  have hα : φ ≫ α = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_id]
    exact hs)
  have hβ : φ ≫ β = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_id]
    exact ht)
  have hp : IsLocalRing.closedPoint K = (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  rw [hp] at h
  have hI := congrArg (fun p : PrimeSpectrum R ↦ p.asIdeal) h
  change Ideal.comap α.hom (⊥ : Ideal K) = Ideal.comap β.hom (⊥ : Ideal K) at hI
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  have hαr : α (φ (α r)) = α r := by
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of K ↦ q (α r)) hα
  have hβr : β (φ (α r)) = α r := by
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of K ↦ q (α r)) hβ
  have hm : r - φ (α r) ∈ Ideal.comap α.hom (⊥ : Ideal K) := by
    change α (r - φ (α r)) ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot, map_sub, hαr, sub_self]
  rw [hI] at hm
  change β (r - φ (α r)) ∈ (⊥ : Ideal K) at hm
  rw [Ideal.mem_bot, map_sub, hβr] at hm
  exact (sub_eq_zero.mp hm).symm

theorem section_eq_of_point_eq_affine {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of K)) (s t : Spec (CommRingCat.of K) ⟶ X)
    (hs : s ≫ f = 𝟙 _) (ht : t ≫ f = 𝟙 _)
    (h : s (IsLocalRing.closedPoint K) = t (IsLocalRing.closedPoint K)) : s = t := by
  let e := X.isoSpec
  apply (cancel_mono e.hom).mp
  apply section_eq_of_point_eq (e.inv ≫ f)
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht
  · exact congrArg e.hom h

end ManuscriptAudit.AffineRationalSectionUniqueness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineRationalSectionUniqueness.section_eq_of_point_eq,
      ``ManuscriptAudit.AffineRationalSectionUniqueness.section_eq_of_point_eq_affine] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
