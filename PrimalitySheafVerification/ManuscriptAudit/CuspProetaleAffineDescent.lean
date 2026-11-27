import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.AlgebraicGeometry.Limits
import PrimalitySheafVerification.ManuscriptAudit.AffineWeaklyEtaleRelativeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleDescent

/-!
# Affine weakly étale descent along cusp normalization in prime characteristic

Pulling back an actual affine weakly étale object through reverse Frobenius
descends it along the cusp normalization, by the weakly étale Frobenius square.
-/

namespace ManuscriptAudit.CuspProetaleAffineDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open ManuscriptAudit.AffineAbsoluteFrobenius
open ManuscriptAudit.CuspPunctured
open ManuscriptAudit.CuspEtaleDescent (reverseFrobeniusMap normalization_comp_reverseFrobenius)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]
variable (p : ℕ) [pPrime : Fact p.Prime] [kCharP : CharP K p]

private abbrev Normalization : Scheme.{u} := Spec (CommRingCat.of (Polynomial K))
private abbrev Cusp : Scheme.{u} := Spec (CommRingCat.of (CuspSubalgebra K))

local instance polynomialCharP : CharP (Polynomial K) p :=
  charP_of_injective_algebraMap (algebraMap K (Polynomial K)).injective p

/-- The base change of an affine weakly étale algebra along reverse Frobenius descends it through
normalization. The square explicitly compares the descended morphism with the given object. -/
theorem affine_weaklyEtale_algebra_descends (B : Type u) [CommRing B] [CharP B p]
    [Algebra (Polynomial K) B]
    [WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B)))] :
    ∃ (R : CommRingCat.{u}) (d : Spec R ⟶ Cusp K), WeaklyEtale d ∧
      ∃ j : Spec (CommRingCat.of B) ⟶ Spec R,
        IsPullback j (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B)))
          d (CuspScheme.cuspMap K) := by
  let f : Spec (CommRingCat.of B) ⟶ Normalization K :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B))
  let ρ := reverseFrobeniusMap K p
  let ν := CuspScheme.cuspMap K
  letI : WeaklyEtale f := inferInstanceAs
    (WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B))))
  let D := pullback f ρ
  letI : IsAffine D := inferInstanceAs (IsAffine (pullback f ρ))
  let e : D ≅ Spec Γ(D, ⊤) := D.isoSpec
  let d : Spec Γ(D, ⊤) ⟶ Cusp K := e.inv ≫ pullback.snd f ρ
  letI : WeaklyEtale d := by
    change WeaklyEtale (e.inv ≫ pullback.snd f ρ)
    infer_instance
  have hFrob : IsPullback (frobeniusMap B p) f f (ν ≫ ρ) := by
    rw [show ν ≫ ρ = frobeniusMap (Polynomial K) p from normalization_comp_reverseFrobenius K p]
    exact AffineWeaklyEtaleRelativeFrobenius.frobenius_square_isPullback (Polynomial K) B p
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
set_option backward.isDefEq.respectTransparency false in
/-- Every affine weakly étale morphism over the normalization comes from an actual pullback square
along the cusp map. The empty affine scheme descends as the empty affine scheme. -/
theorem affine_weaklyEtale_descends (T : CommRingCat.{u}) (f : Spec T ⟶ Normalization K) [WeaklyEtale f] :
    ∃ (R : CommRingCat.{u}) (d : Spec R ⟶ Cusp K), WeaklyEtale d ∧
      ∃ j : Spec T ⟶ Spec R, IsPullback j f d (CuspScheme.cuspMap K) := by
  rcases subsingleton_or_nontrivial T with h | h
  · letI : Subsingleton T := h
    letI : IsEmpty (Spec T) := inferInstanceAs (IsEmpty (PrimeSpectrum T))
    let ν := CuspScheme.cuspMap K
    let d : Spec T ⟶ Cusp K := (isInitialOfIsEmpty (X := Spec T)).to (Cusp K)
    letI : WeaklyEtale d := inferInstance
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
    have hmap : Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) T)) = f := hk
    letI : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) T))) :=
      hmap.symm ▸ inferInstanceAs (WeaklyEtale f)
    obtain ⟨R, d, hd, j, hj⟩ := affine_weaklyEtale_algebra_descends K p T
    refine ⟨R, d, hd, j, ?_⟩
    rw [← hmap]
    exact hj

end

end ManuscriptAudit.CuspProetaleAffineDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProetaleAffineDescent.affine_weaklyEtale_algebra_descends,
      ``ManuscriptAudit.CuspProetaleAffineDescent.affine_weaklyEtale_descends] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
