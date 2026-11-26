import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Absolute Frobenius on an affine scheme

In positive prime characteristic the actual absolute Frobenius is
integral, surjective and universally injective. The field-point proof
uses injectivity of Frobenius in fields of that characteristic.
-/

namespace ManuscriptAudit.AffineAbsoluteFrobenius

open AlgebraicGeometry CategoryTheory CategoryTheory.MorphismProperty Polynomial

noncomputable section

universe u

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

private abbrev frobeniusArrow : CommRingCat.of R ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (frobenius R p)

/-- The absolute Frobenius of the actual affine scheme `Spec R`. -/
def frobeniusMap : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (frobeniusArrow R p)

theorem frobeniusMap_integral : IsIntegralHom (frobeniusMap R p) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  intro x
  have hp : p.Prime := Fact.out
  refine ⟨(X : Polynomial R) ^ p - C x, monic_X_pow_sub_C x hp.pos.ne', ?_⟩
  change eval₂ (frobenius R p) x ((X : Polynomial R) ^ p - C x) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, frobenius_def, sub_self]

/-- Frobenius fixes each prime ideal of the underlying spectrum. -/
theorem frobenius_primeSpectrum_fixed (x : PrimeSpectrum R) :
    PrimeSpectrum.comap (frobenius R p) x = x := by
  apply PrimeSpectrum.ext_iff.mpr
  ext a
  change a ^ p ∈ x.asIdeal ↔ a ∈ x.asIdeal
  exact (inferInstance : x.asIdeal.IsPrime).pow_mem_iff_mem p (show p.Prime from Fact.out).pos

theorem frobeniusMap_surjective : Surjective (frobeniusMap R p) := by
  rw [surjective_iff]
  intro x
  refine ⟨x, ?_⟩
  exact frobenius_primeSpectrum_fixed R p x

theorem frobeniusMap_universally_injective : UniversallyInjective (frobeniusMap R p) := by
  have hp : p.Prime := Fact.out
  apply ((tfae_universallyInjective (frobeniusMap R p)).out 1 0).mp
  intro F _ f g h
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  have he : Spec.map (frobeniusArrow R p ≫ f') = Spec.map (frobeniusArrow R p ≫ g') := by
    simpa only [Spec.map_comp, frobeniusMap] using h
  have hRing := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  have hpzero : (p : F) = 0 := by
    rw [← map_natCast f'.hom, CharP.cast_eq_zero R p, map_zero]
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
  have heq : f'.hom = g'.hom := by
    ext a
    have hpow := DFunLike.congr_fun hRing a
    change f'.hom (a ^ p) = g'.hom (a ^ p) at hpow
    rw [map_pow, map_pow] at hpow
    by_contra hne
    have hz : (f'.hom a - g'.hom a) ^ p = 0 := by
      change frobenius F p (f'.hom a - g'.hom a) = 0
      simp only [map_sub, frobenius_def, hpow, sub_self]
    exact (pow_ne_zero p (sub_ne_zero.mpr hne)) hz
  rw [CommRingCat.hom_ext heq]

/-- Every base change of the actual affine Frobenius is a homeomorphism. -/
theorem frobeniusMap_universal_homeomorphism :
    (topologically @IsHomeomorph).universally (frobeniusMap R p) := by
  intro X' Y' i₁ i₂ f' h
  letI : IsIntegralHom (frobeniusMap R p) := frobeniusMap_integral R p
  letI : Surjective f' := of_isPullback h.flip (frobeniusMap_surjective R p)
  letI : UniversallyInjective f' := of_isPullback h.flip (frobeniusMap_universally_injective R p)
  letI : UniversallyClosed f' := of_isPullback h.flip
    (inferInstance : UniversallyClosed (frobeniusMap R p))
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, ⟨f'.injective, f'.surjective⟩⟩

end

end ManuscriptAudit.AffineAbsoluteFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineAbsoluteFrobenius.frobeniusMap_integral,
      ``ManuscriptAudit.AffineAbsoluteFrobenius.frobenius_primeSpectrum_fixed,
      ``ManuscriptAudit.AffineAbsoluteFrobenius.frobeniusMap_universally_injective,
      ``ManuscriptAudit.AffineAbsoluteFrobenius.frobeniusMap_universal_homeomorphism] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
