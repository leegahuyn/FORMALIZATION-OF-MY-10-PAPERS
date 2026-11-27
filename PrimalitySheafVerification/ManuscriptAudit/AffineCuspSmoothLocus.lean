import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import PrimalitySheafVerification.ManuscriptAudit.CuspPlaneSmoothness
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured
import PrimalitySheafVerification.ManuscriptAudit.CuspScheme

/-! The actual relative smooth locus of the affine cusp is the puncture
used in the arithmetic small étale calculation. -/

namespace ManuscriptAudit.AffineCuspSmoothLocus

open AlgebraicGeometry CategoryTheory
open CuspPunctured (CuspSubalgebra cuspSquare paper2_cusp_punctured_coordinate_equiv)
open CuspScheme (cuspMap inclusion paper2_cusp_map_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev A := CuspSubalgebra K
abbrev cusp := Spec (CommRingCat.of (A K))
private abbrev B := Localization.Away (cuspSquare K)
abbrev punctured := Spec (CommRingCat.of (B K))

def cuspToBase : cusp K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (A K)))

instance cusp_locallyOfFinitePresentation : LocallyOfFinitePresentation (cuspToBase K) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (algebraMap K (A K)))).mpr
  exact RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.equiv (CuspDelta.paper2_cusp_coordinate_presentation K))

private abbrev cuspBasic : (cusp K).Opens := PrimeSpectrum.basicOpen (cuspSquare K)

def puncturedToCusp : punctured K ⟶ cusp K :=
  Spec.map (CommRingCat.ofHom (algebraMap (A K) (B K)))

instance punctured_open : IsOpenImmersion (puncturedToCusp K) :=
  IsOpenImmersion.of_isLocalization (S := B K) (cuspSquare K)

private theorem punctured_range :
    Set.range (puncturedToCusp K) = (↑(cuspBasic K) : Set (cusp K)) := by
  change Set.range (PrimeSpectrum.comap (algebraMap (A K) (B K))) =
    ↑(PrimeSpectrum.basicOpen (cuspSquare K))
  exact PrimeSpectrum.localization_away_comap_range (B K) (cuspSquare K)

private theorem polynomial_prime_over_origin (p : PrimeSpectrum (Polynomial K))
    (hp : (Polynomial.X : Polynomial K) ^ 2 ∈ p.asIdeal) :
    p.asIdeal = RingHom.ker (Polynomial.constantCoeff : Polynomial K →+* K) := by
  have hx : (Polynomial.X : Polynomial K) ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 2 hp
  have hMax : (RingHom.ker (Polynomial.constantCoeff : Polynomial K →+* K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff
      (fun a => ⟨Polynomial.C a, by simp⟩)
  apply (hMax.eq_of_le p.isPrime.ne_top ?_).symm
  rw [Polynomial.ker_constantCoeff]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)

private theorem lift_prime_square (x : cusp K) (hx : cuspSquare K ∈ x.asIdeal) :
    ∃ p : PrimeSpectrum (Polynomial K), cuspMap K p = x ∧
      (Polynomial.X : Polynomial K) ^ 2 ∈ p.asIdeal := by
  have hs := paper2_cusp_map_surjective K
  rw [surjective_iff] at hs
  obtain ⟨p, hp⟩ := hs x
  refine ⟨p, hp, ?_⟩
  have h : cuspSquare K ∈ (cuspMap K p).asIdeal := by simpa only [hp] using hx
  rw [cuspMap, Spec.map_apply] at h
  exact h

private theorem omitted_prime_unique (x y : cusp K)
    (hx : cuspSquare K ∈ x.asIdeal) (hy : cuspSquare K ∈ y.asIdeal) : x = y := by
  obtain ⟨p, hp, hpx⟩ := lift_prime_square K x hx
  obtain ⟨q, hq, hqy⟩ := lift_prime_square K y hy
  have h : p = q := PrimeSpectrum.ext ((polynomial_prime_over_origin K p hpx).trans
    (polynomial_prime_over_origin K q hqy).symm)
  exact hp.symm.trans ((congrArg (cuspMap K) h).trans hq)

private theorem puncture_smooth : Smooth (puncturedToCusp K ≫ cuspToBase K) := by
  let e : Polynomial K →ₐ[K] LaurentPolynomial K := Polynomial.toLaurentAlg
  letI : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  letI : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth (Polynomial K) (LaurentPolynomial K) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial K)
  letI : Algebra.Smooth K (LaurentPolynomial K) :=
    Algebra.Smooth.comp K (Polynomial K) (LaurentPolynomial K)
  have h : Algebra.Smooth K (B K) :=
    Algebra.Smooth.of_equiv (paper2_cusp_punctured_coordinate_equiv K).symm
  have he : puncturedToCusp K ≫ cuspToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (B K))) := by
    unfold puncturedToCusp cuspToBase
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq K (A K) (B K)).symm
  rw [he]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr h)

theorem cusp_not_smooth : ¬ Smooth (cuspToBase K) := by
  intro h
  have hr : (algebraMap K (A K)).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h
  letI : Algebra.Smooth K (A K) := RingHom.smooth_algebraMap.mp hr
  exact CuspPlaneSmoothness.cuspPlane_not_smooth K
    (Algebra.Smooth.of_equiv (CuspDelta.paper2_cusp_coordinate_presentation K).symm)

/-- The genuine relative smooth locus of the cusp is precisely D(t²). -/
theorem smoothLocus_eq_basicOpen :
    (cuspToBase K).smoothLocus = cuspBasic K := by
  have hAway : (↑(cuspBasic K) : Set (cusp K)) ⊆
      (↑((cuspToBase K).smoothLocus) : Set (cusp K)) := by
    rw [← punctured_range]
    rintro _ ⟨a, rfl⟩
    letI : Smooth (puncturedToCusp K ≫ cuspToBase K) := puncture_smooth K
    apply ((puncturedToCusp K).mem_preimage).mp
    rw [(puncturedToCusp K).preimage_smoothLocus_eq (cuspToBase K),
      Scheme.Hom.smoothLocus_eq_top]
    trivial
  refine le_antisymm ?_ hAway
  intro x hx
  by_contra h
  have h'x : cuspSquare K ∈ x.asIdeal :=
    Classical.not_not.mp (fun hs => h ((PrimeSpectrum.mem_basicOpen _ _).mpr hs))
  apply cusp_not_smooth K
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro y _
  by_cases hy : y ∈ cuspBasic K
  · exact hAway hy
  · have h'y : cuspSquare K ∈ y.asIdeal :=
      Classical.not_not.mp (fun hs => hy ((PrimeSpectrum.mem_basicOpen _ _).mpr hs))
    rw [omitted_prime_unique K y x h'y h'x]
    exact hx

/-- The actual smooth-locus scheme equals the localization used for arithmetic H¹. -/
def smoothLocusIso :
    (cuspToBase K).smoothLocus.toScheme ≅ punctured K :=
  IsOpenImmersion.isoOfRangeEq (cuspToBase K).smoothLocus.ι (puncturedToCusp K) (by
    rw [Scheme.Opens.range_ι, smoothLocus_eq_basicOpen, punctured_range])

end
end ManuscriptAudit.AffineCuspSmoothLocus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineCuspSmoothLocus.cusp_not_smooth,
      ``ManuscriptAudit.AffineCuspSmoothLocus.smoothLocus_eq_basicOpen,
      ``ManuscriptAudit.AffineCuspSmoothLocus.smoothLocusIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
