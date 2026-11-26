import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import PrimalitySheafVerification.ManuscriptAudit.AffineFrobeniusPullback
import PrimalitySheafVerification.ManuscriptAudit.CuspFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CuspScheme

/-!
# Affine étale descent along the cusp normalization in prime characteristic

The factorization of Frobenius through the cusp gives a reverse map.
An affine étale object descends by pullback along that map. Its further
pullback to the normalization is isomorphic to the original object by
the affine étale Frobenius square.
-/

namespace ManuscriptAudit.CuspEtaleDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open ManuscriptAudit.AffineAbsoluteFrobenius
open ManuscriptAudit.CuspFrobenius ManuscriptAudit.CuspPunctured

universe u

noncomputable section

variable (K : Type u) [Field K]
variable (p : ℕ) [pPrime : Fact p.Prime] [kCharP : CharP K p]

private abbrev Normalization : Scheme.{u} := Spec (CommRingCat.of (Polynomial K))
private abbrev Cusp : Scheme.{u} := Spec (CommRingCat.of (CuspSubalgebra K))

local instance polynomialCharP : CharP (Polynomial K) p :=
  charP_of_injective_algebraMap (algebraMap K (Polynomial K)).injective p

/-- The reverse scheme map induced by the factorization of polynomial Frobenius. -/
def reverseFrobeniusMap : Cusp K ⟶ Normalization K :=
  Spec.map (CommRingCat.ofHom (normalizationFrobeniusToCusp K p))

theorem normalization_comp_reverseFrobenius :
    CuspScheme.cuspMap K ≫ reverseFrobeniusMap K p = frobeniusMap (Polynomial K) p := by
  have hRing : CommRingCat.ofHom (normalizationFrobeniusToCusp K p) ≫ CuspScheme.inclusion K =
      CommRingCat.ofHom (frobenius (Polynomial K) p) :=
    CommRingCat.hom_ext (inclusion_comp_normalizationFrobenius K p)
  change Spec.map (CuspScheme.inclusion K) ≫
    Spec.map (CommRingCat.ofHom (normalizationFrobeniusToCusp K p)) =
      Spec.map (CommRingCat.ofHom (frobenius (Polynomial K) p))
  rw [← Spec.map_comp, hRing]

/-- The base change of an affine étale algebra along reverse Frobenius descends it through
normalization. The square explicitly compares the descended morphism with the given object. -/
theorem affine_etale_algebra_descends (B : Type u) [CommRing B] [CharP B p]
    [Algebra (Polynomial K) B] [Algebra.Etale (Polynomial K) B] :
    ∃ (R : CommRingCat.{u}) (d : Spec R ⟶ Cusp K), Etale d ∧
      ∃ j : Spec (CommRingCat.of B) ⟶ Spec R,
        IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B)))
          d (CuspScheme.cuspMap K) := by
  let f : Spec (CommRingCat.of B) ⟶ Normalization K :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B))
  let ρ := reverseFrobeniusMap K p
  let ν := CuspScheme.cuspMap K
  letI : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let D := pullback f ρ
  letI : IsAffine D := inferInstanceAs (IsAffine (pullback f ρ))
  let e : D ≅ Spec Γ(D, ⊤) := D.isoSpec
  let d : Spec Γ(D, ⊤) ⟶ Cusp K := e.inv ≫ pullback.snd f ρ
  letI : Etale d := by
    change Etale (e.inv ≫ pullback.snd f ρ)
    infer_instance
  have hFrob : IsPullback (frobeniusMap B p) f f (ν ≫ ρ) := by
    rw [show ν ≫ ρ = frobeniusMap (Polynomial K) p from normalization_comp_reverseFrobenius K p]
    exact AffineFrobeniusPullback.frobenius_square_isPullback (Polynomial K) B p
  let a : Spec (CommRingCat.of B) ≅ pullback (pullback.snd f ρ) ν :=
    hFrob.isoPullback ≪≫ (pullbackLeftPullbackSndIso f ρ ν).symm
  have ha : a.hom ≫ pullback.snd (pullback.snd f ρ) ν = f := by
    change (hFrob.isoPullback.hom ≫ (pullbackLeftPullbackSndIso f ρ ν).inv) ≫ _ = _
    rw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hFrob.isoPullback_hom_snd]
  let j : Spec (CommRingCat.of B) ⟶ Spec Γ(D, ⊤) :=
    a.hom ≫ pullback.fst (pullback.snd f ρ) ν ≫ e.hom
  refine ⟨Γ(D, ⊤), d, inferInstance, j, ?_⟩
  refine (IsPullback.of_hasPullback (pullback.snd f ρ) ν).of_iso'
    a e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [j]
  · simpa only [Iso.refl_hom, Category.comp_id] using ha
  · simp [d]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

include p pPrime kCharP in
/-- Every affine étale morphism over the normalization comes from an actual pullback square
along the cusp map. The empty affine scheme descends as the empty affine scheme. -/
theorem affine_etale_descends (T : CommRingCat.{u}) (f : Spec T ⟶ Normalization K) [Etale f] :
    ∃ (R : CommRingCat.{u}) (d : Spec R ⟶ Cusp K), Etale d ∧
      ∃ j : Spec T ⟶ Spec R, IsPullback j f d (CuspScheme.cuspMap K) := by
  rcases subsingleton_or_nontrivial T with h | h
  · letI : Subsingleton T := h
    letI : IsEmpty (Spec T) := inferInstanceAs (IsEmpty (PrimeSpectrum T))
    let ν := CuspScheme.cuspMap K
    let d : Spec T ⟶ Cusp K := (isInitialOfIsEmpty (X := Spec T)).to (Cusp K)
    letI : Etale d := inferInstance
    have hcomm : 𝟙 (Spec T) ≫ d = f ≫ ν := (isInitialOfIsEmpty (X := Spec T)).hom_ext _ _
    let j : Spec T ⟶ pullback d ν := pullback.lift (𝟙 (Spec T)) f hcomm
    letI : IsEmpty ↥(pullback d ν) := (pullback.fst d ν).base.hom.1.isEmpty
    letI : IsIso j := inferInstance
    refine ⟨T, d, inferInstance, 𝟙 _, IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso j) ?_ ?_⟩
    · exact pullback.lift_fst (𝟙 (Spec T)) f hcomm
    · exact pullback.lift_snd (𝟙 (Spec T)) f hcomm
  · letI : Nontrivial T := h
    obtain ⟨k, hk⟩ := Spec.map_surjective f
    letI : Algebra (Polynomial K) T := k.hom.toAlgebra
    have hpzero : (p : T) = 0 := by
      rw [← map_natCast k.hom, CharP.cast_eq_zero (Polynomial K) p, map_zero]
    letI : CharP T p := (CharP.charP_iff_prime_eq_zero (show p.Prime from Fact.out)).mpr hpzero
    have hkEtale : k.hom.Etale := by
      apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      rw [hk]
      infer_instance
    letI : Algebra.Etale (Polynomial K) T := RingHom.etale_algebraMap.mp hkEtale
    have hmap : Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) T)) = f := hk
    simpa only [hmap] using affine_etale_algebra_descends K p T

end

end ManuscriptAudit.CuspEtaleDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspEtaleDescent.normalization_comp_reverseFrobenius,
      ``ManuscriptAudit.CuspEtaleDescent.affine_etale_algebra_descends,
      ``ManuscriptAudit.CuspEtaleDescent.affine_etale_descends] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
