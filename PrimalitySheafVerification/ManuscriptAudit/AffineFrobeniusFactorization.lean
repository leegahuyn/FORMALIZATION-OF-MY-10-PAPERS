import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Affine maps factoring Frobenius

A ring map whose two composites with a map in the opposite direction are
pth powers induces a universal homeomorphism of affine schemes. The
proof checks integrality and field points on the actual scheme map.
-/

namespace ManuscriptAudit.AffineFrobeniusFactorization

open AlgebraicGeometry CategoryTheory CategoryTheory.MorphismProperty Polynomial

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
variable (p : ℕ) [Fact p.Prime]

/-- The actual map on spectra induced by a ring homomorphism. -/
abbrev specMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMap_integral_of_power_lifts (h : ∀ b : B, ∃ a : A, f a = b ^ p) :
    IsIntegralHom (specMap f) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  intro b
  obtain ⟨a, ha⟩ := h b
  have hp : p.Prime := Fact.out
  refine ⟨(X : Polynomial A) ^ p - C a, monic_X_pow_sub_C a hp.pos.ne', ?_⟩
  change eval₂ f b ((X : Polynomial A) ^ p - C a) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ha, sub_self]

theorem specMap_surjective_of_factors_power (g : B →+* A) (h : ∀ a, g (f a) = a ^ p) :
    Surjective (specMap f) := by
  rw [surjective_iff]
  change Function.Surjective (PrimeSpectrum.comap f)
  intro x
  refine ⟨PrimeSpectrum.comap g x, ?_⟩
  change PrimeSpectrum.comap f (PrimeSpectrum.comap g x) = x
  apply PrimeSpectrum.ext_iff.mpr
  ext a
  change g (f a) ∈ x.asIdeal ↔ a ∈ x.asIdeal
  rw [h]
  exact x.isPrime.pow_mem_iff_mem p (show p.Prime from Fact.out).pos

theorem specMap_universallyInjective_of_power_lifts (hpB : (p : B) = 0)
    (h : ∀ b : B, ∃ a : A, f a = b ^ p) : UniversallyInjective (specMap f) := by
  have hp : p.Prime := Fact.out
  apply ((tfae_universallyInjective (specMap f)).out 1 0).mp
  intro F _ x y hxy
  obtain ⟨x', rfl⟩ := Spec.map_surjective x
  obtain ⟨y', rfl⟩ := Spec.map_surjective y
  have he : Spec.map (CommRingCat.ofHom f ≫ x') =
      Spec.map (CommRingCat.ofHom f ≫ y') := by
    simpa only [Spec.map_comp] using hxy
  have hRing := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  have hpzero : (p : F) = 0 := by
    rw [← map_natCast x'.hom, hpB, map_zero]
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
  have heq : x'.hom = y'.hom := by
    ext b
    obtain ⟨a, ha⟩ := h b
    have hpow := DFunLike.congr_fun hRing a
    change x'.hom (f a) = y'.hom (f a) at hpow
    rw [ha, map_pow, map_pow] at hpow
    by_contra hne
    have hz : (x'.hom b - y'.hom b) ^ p = 0 := by
      change frobenius F p (x'.hom b - y'.hom b) = 0
      simp only [map_sub, frobenius_def, hpow, sub_self]
    exact pow_ne_zero p (sub_ne_zero.mpr hne) hz
  rw [CommRingCat.hom_ext heq]

/-- A ring map factoring pth powers on both sides gives a universal
homeomorphism of the corresponding affine schemes. -/
theorem specMap_universalHomeomorphism (hpB : (p : B) = 0) (g : B →+* A)
    (ha : ∀ a, g (f a) = a ^ p) (hb : ∀ b, f (g b) = b ^ p) :
    (topologically @IsHomeomorph).universally (specMap f) := by
  have hLift (b : B) : ∃ a : A, f a = b ^ p := ⟨g b, hb b⟩
  intro X' Y' i₁ i₂ f' h
  letI : IsIntegralHom (specMap f) := specMap_integral_of_power_lifts f p hLift
  letI : Surjective f' := of_isPullback h.flip (specMap_surjective_of_factors_power f p g ha)
  letI : UniversallyInjective f' :=
    of_isPullback h.flip (specMap_universallyInjective_of_power_lifts f p hpB hLift)
  letI : UniversallyClosed f' := of_isPullback h.flip
    (inferInstance : UniversallyClosed (specMap f))
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, ⟨f'.injective, f'.surjective⟩⟩

end

end ManuscriptAudit.AffineFrobeniusFactorization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineFrobeniusFactorization.specMap_integral_of_power_lifts,
      ``ManuscriptAudit.AffineFrobeniusFactorization.specMap_surjective_of_factors_power,
      ``ManuscriptAudit.AffineFrobeniusFactorization.specMap_universallyInjective_of_power_lifts,
      ``ManuscriptAudit.AffineFrobeniusFactorization.specMap_universalHomeomorphism] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
