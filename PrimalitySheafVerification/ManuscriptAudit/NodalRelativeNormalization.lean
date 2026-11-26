import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization

/-! The relative normalization of the actual punctured affine node has
coordinate algebra K[t] over the original nodal coordinate ring. -/

namespace ManuscriptAudit.NodalRelativeNormalization

open NodalConductor NodalAwayNormalization

noncomputable section

variable (K : Type*) [Field K]

abbrev A := coordinates K
abbrev B := Polynomial K
abbrev L := Localization.Away (nodeX K)
abbrev F := FractionRing (B K)

private theorem conductor_ne_zero : x K ≠ 0 := by
  intro h
  have hc := congrArg Polynomial.constantCoeff h
  simpa [x] using hc

private theorem fraction_conductor_isUnit :
    IsUnit (algebraMap (A K) (F K) (nodeX K)) := by
  apply isUnit_iff_ne_zero.mpr
  change algebraMap (B K) (F K) (x K) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective (B K) (F K))).mpr
    (conductor_ne_zero K)

/-- The punctured affine node embeds in the common fraction field. -/
def punctureToFraction : L K →ₐ[A K] F K :=
  IsLocalization.Away.liftAlgHom (nodeX K) (f := Algebra.ofId (A K) (F K))
    (fraction_conductor_isUnit K)

theorem punctureToFraction_injective : Function.Injective (punctureToFraction K) := by
  letI : IsFractionRing (A K) (F K) := NodalNormalization.common_fraction_field K
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (nodeX K))
    (punctureToFraction K).toRingHom
  intro a ha
  change punctureToFraction K (algebraMap (A K) (L K) a) = 0 at ha
  rw [AlgHom.commutes] at ha
  have hzero : a = 0 := (IsFractionRing.injective (A K) (F K)) (ha.trans (map_zero _).symm)
  rw [hzero, map_zero]

private theorem normalize_algebraMap (a : A K) :
    normalizationEquiv K (algebraMap (A K) (L K) a) =
      algebraMap (B K) (Localization.Away (x K)) a.val := by
  change (Localization.awayMapₐ (coordinates K).val (nodeX K))
    (algebraMap (A K) (L K) a) = _
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq] <;> rfl

/-- Pull polynomial functions back to the actual puncture via the conductor
localization equivalence. -/
def polynomialToPuncture : B K →ₐ[A K] L K where
  __ := (normalizationEquiv K).symm.toRingHom.comp
    (algebraMap (B K) (Localization.Away (x K)))
  commutes' a := by
    apply (normalizationEquiv K).injective
    change normalizationEquiv K ((normalizationEquiv K).symm
      (algebraMap (B K) (Localization.Away (x K)) a.val)) =
      normalizationEquiv K (algebraMap (A K) (L K) a)
    rw [AlgEquiv.apply_symm_apply, normalize_algebraMap]

private theorem fraction_agrees_polynomial (b : B K) :
    punctureToFraction K (polynomialToPuncture K b) = algebraMap (B K) (F K) b := by
  let a : A K := ⟨x K * b, x_mul_mem_coordinates K b⟩
  have hL : polynomialToPuncture K b * algebraMap (A K) (L K) (nodeX K) =
      algebraMap (A K) (L K) a := by
    apply (normalizationEquiv K).injective
    rw [map_mul, normalize_algebraMap, normalize_algebraMap]
    change (normalizationEquiv K) ((normalizationEquiv K).symm
      (algebraMap (B K) (Localization.Away (x K)) b)) *
      algebraMap (B K) (Localization.Away (x K)) (x K) =
      algebraMap (B K) (Localization.Away (x K)) (x K * b)
    rw [AlgEquiv.apply_symm_apply, map_mul, mul_comm]
  have hF := congrArg (punctureToFraction K) hL
  simp only [map_mul, AlgHom.commutes] at hF
  change punctureToFraction K (polynomialToPuncture K b) *
      algebraMap (B K) (F K) (x K) = algebraMap (B K) (F K) (x K * b) at hF
  rw [map_mul, mul_comm] at hF
  exact mul_left_cancel₀ (by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (B K) (F K))).mpr
      (conductor_ne_zero K)) hF

private theorem polynomialToPuncture_isIntegral (h2 : (2 : K) ≠ 0) (b : B K) :
    IsIntegral (A K) (polynomialToPuncture K b) := by
  letI : Module.Finite (A K) (B K) := NodalNormalization.normalization_finite K h2
  letI : Algebra.IsIntegral (A K) (B K) := Algebra.IsIntegral.of_finite _ _
  exact (Algebra.IsIntegral.isIntegral b).map (polynomialToPuncture K)

/-- The relative integral closure in the actual conductor puncture is the
polynomial normalization, as an algebra over the original node. -/
def polynomialEquivIntegralClosure (h2 : (2 : K) ≠ 0) :
    B K ≃ₐ[A K] integralClosure (A K) (L K) := by
  let f : B K →ₐ[A K] integralClosure (A K) (L K) :=
    (polynomialToPuncture K).codRestrict _ (polynomialToPuncture_isIntegral K h2)
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have h := congrArg (fun u : integralClosure (A K) (L K) =>
      punctureToFraction K u.val) hab
    change punctureToFraction K (polynomialToPuncture K a) =
      punctureToFraction K (polynomialToPuncture K b) at h
    rw [fraction_agrees_polynomial, fraction_agrees_polynomial] at h
    exact (IsFractionRing.injective (B K) (F K)) h
  · intro a
    letI : IsIntegralClosure (B K) (A K) (F K) :=
      NodalNormalization.polynomial_is_integral_closure K h2
    have h : IsIntegral (A K) (punctureToFraction K a.val) :=
      (show IsIntegral (A K) a.val from a.property).map (punctureToFraction K)
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B K)).mp h
    refine ⟨b, Subtype.ext ((punctureToFraction_injective K) ?_)⟩
    change punctureToFraction K (polynomialToPuncture K b) = punctureToFraction K a.val
    rw [fraction_agrees_polynomial]
    exact hb

end
end ManuscriptAudit.NodalRelativeNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalRelativeNormalization.punctureToFraction_injective,
      ``ManuscriptAudit.NodalRelativeNormalization.polynomialEquivIntegralClosure] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
