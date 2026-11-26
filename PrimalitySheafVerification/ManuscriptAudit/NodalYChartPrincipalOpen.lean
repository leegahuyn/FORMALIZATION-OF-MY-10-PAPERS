import Lean.Util.CollectAxioms
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection

/-! The actual Y-chart ring is a normal PID, and the overlap in the
small étale site is its principal open at the displayed x coordinate. -/

namespace ManuscriptAudit.NodalYChartPrincipalOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure NodalProperYChart NodalYChartImmersion
open NodalYChartOverlap (overlapRing)
open NodalChartIntersection (intersection_snd_opensRange)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K]

private abbrev denominator : Polynomial K := 1 - Polynomial.X ^ 2
private abbrev localized := Localization.Away (denominator K)

private theorem denominator_ne_zero : denominator K ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (0 : K)) h
  exact one_ne_zero (by simpa [denominator] using he)

private theorem denominator_good : Submonoid.powers (denominator K) ≤ (Polynomial K)⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n (denominator_ne_zero K))

private instance localizedDomain : IsDomain (localized K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (localized K) (denominator_good K)

private instance localizedPID : IsPrincipalIdealRing (localized K) := ⟨fun I => by
  rw [← IsLocalization.map_under (Submonoid.powers (denominator K)) (localized K) I]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (localized K))
    (inferInstance : (I.under (Polynomial K)).IsPrincipal)⟩

/-- The affine coordinate ring of the Y-chart is an integral domain. -/
instance yDomain : IsDomain (yCoordinateRing K) := by
  let e := (coordinateEquiv K).toRingEquiv
  apply isDomain_iff_noZeroDivisors_and_nontrivial.mpr
  refine ⟨⟨?_⟩, ⟨⟨0, 1, ?_⟩⟩⟩
  · intro a b hab
    have h : e a * e b = 0 := by rw [← map_mul, hab, map_zero]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (e.injective (h.trans (map_zero e).symm))
    · exact Or.inr (e.injective (h.trans (map_zero e).symm))
  · intro h
    exact zero_ne_one (by simpa using congrArg e h : (0 : localized K) = 1)

/-- Every ideal of the actual Y-chart ring is principal. -/
instance yPID : IsPrincipalIdealRing (yCoordinateRing K) :=
  IsPrincipalIdealRing.of_surjective (coordinateEquiv K).symm
    (coordinateEquiv K).symm.surjective

/-- The actual overlap coordinate is nonzero in the Y-chart ring. -/
theorem coordinate_ne_zero : xCoeff K ≠ 0 := by
  intro h
  have he := congrArg (coordinateEquiv K) h
  change coordinateEquiv K (algebraMap (Polynomial K) (yCoordinateRing K) Polynomial.X) =
    coordinateEquiv K 0 at he
  rw [AlgEquiv.commutes, map_zero] at he
  exact Polynomial.X_ne_zero
    ((IsLocalization.to_map_eq_zero_iff (localized K) (denominator_good K)).mp he)

instance overlapDomain : IsDomain (overlapRing K) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (overlapRing K)
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n (coordinate_ne_zero K))

abbrev principalRingHom : CommRingCat.of (yCoordinateRing K) ⟶ CommRingCat.of (overlapRing K) :=
  CommRingCat.ofHom (algebraMap (yCoordinateRing K) (overlapRing K))

abbrev principalInclusion : Spec (CommRingCat.of (overlapRing K)) ⟶ nodeYChart K :=
  Spec.map (principalRingHom K)

instance principal_open : IsOpenImmersion (principalInclusion K) :=
  IsOpenImmersion.of_isLocalization (S := overlapRing K) (xCoeff K)

private def overlapIso :
    pullback (affineOpen K) (chartOpen K) ≅ Spec (CommRingCat.of (overlapRing K)) := by
  apply IsOpenImmersion.isoOfRangeEq (pullback.snd (affineOpen K) (chartOpen K)) (principalInclusion K)
  change ((pullback.snd (affineOpen K) (chartOpen K)).opensRange : Set (nodeYChart K)) =
    Set.range (principalInclusion K)
  rw [intersection_snd_opensRange]
  exact (PrimeSpectrum.localization_away_comap_range (overlapRing K) (xCoeff K)).symm

private theorem overlapIso_snd :
    (overlapIso K).hom ≫ principalInclusion K = pullback.snd (affineOpen K) (chartOpen K) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

abbrev principalObject : (projectiveNode K).Etale :=
  Scheme.Etale.mk (principalInclusion K ≫ chartOpen K)

abbrev overlapObject : (projectiveNode K).Etale :=
  EtaleOpenIntersection.intersection (affineOpen K) (chartOpen K)

/-- The scheme overlap and principal localization are isomorphic over the projective node. -/
def overlapEtaleIso : overlapObject K ≅ principalObject K :=
  MorphismProperty.Over.isoMk (overlapIso K) (by
    change (overlapIso K).hom ≫ (principalInclusion K ≫ chartOpen K) =
      pullback.fst (affineOpen K) (chartOpen K) ≫ affineOpen K
    rw [← Category.assoc, overlapIso_snd, pullback.condition])

/-- Under this actual site isomorphism the second leg is principal restriction. -/
theorem overlapEtaleIso_snd :
    (overlapEtaleIso K).hom ≫
      (MorphismProperty.Over.homMk (principalInclusion K) rfl :
        principalObject K ⟶ Scheme.Etale.mk (chartOpen K)) =
      EtaleOpenIntersection.sndLeg (affineOpen K) (chartOpen K) := by
  apply MorphismProperty.Over.Hom.ext
  exact overlapIso_snd K

theorem overlap_nonempty : Nonempty (overlapObject K).left := by
  let e := overlapIso K
  have x : Nonempty (Spec (CommRingCat.of (overlapRing K))) := inferInstance
  exact x.map e.inv

theorem overlap_preconnected : PreconnectedSpace (overlapObject K).left := by
  let e := overlapIso K
  have h : IsPreconnected (Set.univ : Set (Spec (CommRingCat.of (overlapRing K)))) :=
    isPreconnected_univ
  refine ⟨?_⟩
  have h' := h.image e.inv e.inv.continuous.continuousOn
  rwa [Set.image_univ, Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso e.inv).2] at h'

end
end ManuscriptAudit.NodalYChartPrincipalOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartPrincipalOpen.yDomain,
      ``ManuscriptAudit.NodalYChartPrincipalOpen.yPID,
      ``ManuscriptAudit.NodalYChartPrincipalOpen.coordinate_ne_zero,
      ``ManuscriptAudit.NodalYChartPrincipalOpen.overlapEtaleIso_snd,
      ``ManuscriptAudit.NodalYChartPrincipalOpen.overlap_nonempty,
      ``ManuscriptAudit.NodalYChartPrincipalOpen.overlap_preconnected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
