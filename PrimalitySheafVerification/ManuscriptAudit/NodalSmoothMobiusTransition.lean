import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusOverlap
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothMobiusY

/-! The two actual Möbius coordinates agree on the normalized
intersection of the smooth nodal charts. -/

namespace ManuscriptAudit.NodalSmoothMobiusTransition

open AlgebraicGeometry CategoryTheory Polynomial
open NodalSmoothMobius (tDenominator tRing uRing uAtT uToT uToT_u mobiusEquiv uAtT_times_tplus)
open NodalSmoothMobiusGm (laurentRing minusRing)
open NodalSmoothMobiusY (uPlusRing plusRing signedCoordinateEquiv negatePolynomial negatePolynomial_X
  yMobiusEquiv yToT)
open NodalSmoothLocusOverlap (puncturedZRing zParameterLocal zParameterLocal_on_affine)
open NodalAwayNormalization (normalizationEquiv)
open NodalAffinePresentation (nodeX)
open NodalConductor (coordinates)
open NodalYChartImmersion (yCoordinateRing xCoeff)
open NodalYChartOverlap (parameterRing tInv denominatorInv denominator_mul_inv t_mul_inv
  yToParameter yToParameter_x)
open NodalYChartOverlapPlane (zParameter)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private abbrev T := NodalYChartOverlap.t K
private abbrev ZRing := puncturedZRing K

private instance : IsScalarTower K (Polynomial K) (laurentRing K) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    ((Polynomial.toLaurentAlg : Polynomial K →ₐ[K] laurentRing K).commutes r).symm

def laurentToZ (h2 : (2 : K) ≠ 0) : laurentRing K →ₐ[K] ZRing K :=
  (normalizationEquiv K).symm.toAlgHom.comp
    ((mobiusEquiv K h2).symm.toAlgHom.comp
      (((NodalSmoothMobiusGm.localizationEquiv K).symm.restrictScalars K).toAlgHom.comp
        (Algebra.algHom K (laurentRing K) (minusRing K))))

def laurentToY (h2 : (2 : K) ≠ 0) : laurentRing K →ₐ[K] yCoordinateRing K :=
  (yMobiusEquiv K h2).symm.toAlgHom.comp
    (((NodalSmoothMobiusY.localizationEquiv K).symm.restrictScalars K).toAlgHom.comp
      (Algebra.algHom K (laurentRing K) (plusRing K)))

private theorem laurent_T_algebraMap :
    algebraMap (Polynomial K) (laurentRing K) Polynomial.X = LaurentPolynomial.T 1 :=
  (LaurentPolynomial.algebraMap_eq_toLaurent Polynomial.X).trans Polynomial.toLaurent_X

private theorem minusEquiv_T :
    (NodalSmoothMobiusGm.localizationEquiv K).symm
      (algebraMap (laurentRing K) (minusRing K) (LaurentPolynomial.T 1)) =
      NodalSmoothMobius.u K := by
  rw [← laurent_T_algebraMap, ← IsScalarTower.algebraMap_apply (Polynomial K) (laurentRing K)
    (minusRing K), (NodalSmoothMobiusGm.localizationEquiv K).symm.commutes] <;> rfl

private theorem plusEquiv_T :
    (NodalSmoothMobiusY.localizationEquiv K).symm
      (algebraMap (laurentRing K) (plusRing K) (LaurentPolynomial.T 1)) =
      algebraMap (Polynomial K) (uPlusRing K) Polynomial.X := by
  rw [← laurent_T_algebraMap, ← IsScalarTower.algebraMap_apply (Polynomial K) (laurentRing K)
    (plusRing K), (NodalSmoothMobiusY.localizationEquiv K).symm.commutes]

private theorem signedEquiv_X :
    signedCoordinateEquiv K (NodalSmoothMobius.u K) =
      -(algebraMap (Polynomial K) (uPlusRing K) Polynomial.X) := by
  change ((signedCoordinateEquiv K : uRing K →+* uPlusRing K)
    (algebraMap (Polynomial K) (uRing K) Polynomial.X)) = _
  unfold signedCoordinateEquiv
  rw [IsLocalization.algEquivOfAlgEquiv_eq_map, IsLocalization.map_eq]
  change algebraMap (Polynomial K) (uPlusRing K) (negatePolynomial K Polynomial.X) = _
  rw [negatePolynomial_X, map_neg]

private theorem signedEquiv_inv_X :
    (signedCoordinateEquiv K).symm (algebraMap (Polynomial K) (uPlusRing K) Polynomial.X) =
      -NodalSmoothMobius.u K := by
  apply (signedCoordinateEquiv K).injective
  rw [AlgEquiv.apply_symm_apply, map_neg, signedEquiv_X, neg_neg]

theorem zGenerator_normalized (h2 : (2 : K) ≠ 0) :
    normalizationEquiv K (laurentToZ K h2 (LaurentPolynomial.T 1)) = uAtT K := by
  change normalizationEquiv K ((normalizationEquiv K).symm
    (uToT K h2 ((NodalSmoothMobiusGm.localizationEquiv K).symm
      (algebraMap (laurentRing K) (minusRing K) (LaurentPolynomial.T 1))))) = _
  rw [AlgEquiv.apply_symm_apply, minusEquiv_T, uToT_u]

set_option maxRecDepth 2048 in
private theorem yGenerator_normalized (h2 : (2 : K) ≠ 0) :
    yToT K (laurentToY K h2 (LaurentPolynomial.T 1)) = -uAtT K := by
  simp only [laurentToY, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.restrictScalars_symm_apply, Algebra.algHom_apply, yMobiusEquiv,
    AlgEquiv.symm_trans_apply]
  have h : ((NodalSmoothMobiusY.localizationEquiv K).symm.restrictScalars K)
      ((Algebra.algHom K (laurentRing K) (plusRing K)) (LaurentPolynomial.T 1)) =
      algebraMap (Polynomial K) (uPlusRing K) Polynomial.X :=
    plusEquiv_T K
  rw [AlgEquiv.apply_symm_apply, h, signedEquiv_inv_X]
  change (uToT K h2) (-NodalSmoothMobius.u K) = -uAtT K
  rw [map_neg, uToT_u]

theorem yGenerator_relation (h2 : (2 : K) ≠ 0) :
    laurentToY K h2 (LaurentPolynomial.T 1) * (xCoeff K + 1) = 1 - xCoeff K := by
  apply (yToT K).injective
  have hx : yToT K (xCoeff K) = NodalSmoothMobius.t K :=
    (yToT K).commutes Polynomial.X
  simp only [map_mul, map_add, map_one, map_sub, yGenerator_normalized K h2, hx,
    neg_mul, uAtT_times_tplus]
  ring

private theorem normalization_on_affine (a : coordinates K) :
    normalizationEquiv K (algebraMap (coordinates K) (ZRing K) a) =
      algebraMap (Polynomial K) (tRing K) a.val := by
  change (Localization.awayMapₐ (coordinates K).val (nodeX K))
    (algebraMap (coordinates K) (ZRing K) a) = _
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq] <;> rfl

private theorem splitUnit : IsUnit (T K ^ 2 - 1) := by
  have h : IsUnit (T K * (T K ^ 2 - 1)) :=
    isUnit_iff_exists_inv.mpr ⟨denominatorInv K, denominator_mul_inv K⟩
  exact (IsUnit.mul_iff.mp h).2

private theorem tPlusUnit : IsUnit (T K + 1) := by
  have h := splitUnit K
  rw [show T K ^ 2 - 1 = (T K - 1) * (T K + 1) by ring] at h
  exact (IsUnit.mul_iff.mp h).2

private def tToParameter : tRing K →ₐ[K] parameterRing K :=
  IsLocalization.Away.liftAlgHom (tDenominator K)
    (f := Algebra.algHom K (Polynomial K) (parameterRing K)) (by
      let g := algebraMap (Polynomial K) (parameterRing K)
      change IsUnit (g (tDenominator K))
      have he : g (tDenominator K) = T K ^ 2 - 1 :=
        (g.map_sub _ _).trans (congrArg₂ (· - ·) (map_pow g Polynomial.X 2) g.map_one)
      exact he.symm ▸ splitUnit K)

private theorem tToParameter_algebraMap (a : Polynomial K) :
    tToParameter K (algebraMap (Polynomial K) (tRing K) a) =
      algebraMap (Polynomial K) (parameterRing K) a := by
  unfold tToParameter
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

private theorem tToParameter_t : tToParameter K (NodalSmoothMobius.t K) = T K :=
  tToParameter_algebraMap K Polynomial.X

private theorem zParameter_factor :
    (tToParameter K).comp (normalizationEquiv K).toAlgHom = zParameterLocal K := by
  apply IsLocalization.algHom_ext (Submonoid.powers (NodalAwayNormalization.nodeX K))
  apply AlgHom.ext
  intro a
  change tToParameter K (normalizationEquiv K (algebraMap (coordinates K) (ZRing K) a)) =
    zParameterLocal K (algebraMap (coordinates K) (ZRing K) a)
  rw [normalization_on_affine, tToParameter_algebraMap, zParameterLocal_on_affine] <;> rfl

private theorem zOverlap_relation (h2 : (2 : K) ≠ 0) :
    zParameterLocal K (laurentToZ K h2 (LaurentPolynomial.T 1)) * (T K + 1) = T K - 1 := by
  have hz := congrArg (fun f : ZRing K →ₐ[K] parameterRing K => f (laurentToZ K h2 (LaurentPolynomial.T 1)))
    (zParameter_factor K)
  change tToParameter K (normalizationEquiv K (laurentToZ K h2 (LaurentPolynomial.T 1))) =
    zParameterLocal K (laurentToZ K h2 (LaurentPolynomial.T 1)) at hz
  rw [zGenerator_normalized] at hz
  rw [← hz]
  have h := congrArg (tToParameter K) (uAtT_times_tplus K)
  simpa only [map_mul, map_add, map_sub, map_one, tToParameter_t] using h

private theorem yOverlap_relation (h2 : (2 : K) ≠ 0) :
    yToParameter K (laurentToY K h2 (LaurentPolynomial.T 1)) * (T K + 1) = T K - 1 := by
  let U := yToParameter K (laurentToY K h2 (LaurentPolynomial.T 1))
  have h : U * (tInv K + 1) = 1 - tInv K := by
    have h := congrArg (yToParameter K) (yGenerator_relation K h2)
    simpa only [map_mul, map_add, map_sub, map_one, yToParameter_x, U] using h
  have hT : T K * tInv K = 1 := t_mul_inv K
  change U * (T K + 1) = T K - 1
  calc
    _ = U * (T K + T K * tInv K) := by rw [hT]
    _ = T K * (U * (tInv K + 1)) := by ring
    _ = T K * (1 - tInv K) := by rw [h]
    _ = _ := by rw [mul_sub, mul_one, hT]

/-- The two actual Laurent-coordinate ring maps agree after both restrictions to the overlap. -/
theorem laurent_maps_agree (h2 : (2 : K) ≠ 0) :
    (zParameterLocal K).comp (laurentToZ K h2) = (yToParameter K).comp (laurentToY K h2) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X : Polynomial K))
  apply Polynomial.algHom_ext
  change zParameterLocal K (laurentToZ K h2 (algebraMap (Polynomial K) (laurentRing K) Polynomial.X)) =
    yToParameter K (laurentToY K h2 (algebraMap (Polynomial K) (laurentRing K) Polynomial.X))
  rw [laurent_T_algebraMap]
  apply (tPlusUnit K).mul_left_inj.mp
  exact (zOverlap_relation K h2).trans (yOverlap_relation K h2).symm

end
end ManuscriptAudit.NodalSmoothMobiusTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothMobiusTransition.zGenerator_normalized,
      ``ManuscriptAudit.NodalSmoothMobiusTransition.yGenerator_relation,
      ``ManuscriptAudit.NodalSmoothMobiusTransition.laurent_maps_agree] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
