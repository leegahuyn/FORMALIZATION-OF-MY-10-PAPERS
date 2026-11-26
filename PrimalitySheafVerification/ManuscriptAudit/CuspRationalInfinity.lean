import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.PowerSeries.Inverse
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification

/-!
# A rational point at infinity on the proper cusp

Over the power-series valuation ring \(K[[s]]\), the generic cusp
parameter \(t=s^{-1}\) has a proper extension to the compactified cusp.
Its specialization at \(s=0\) is a \(K\)-rational point. If that point
were on the affine cusp, the whole valuation-ring map would lie in the
affine chart, making \(s^{-2}\) regular. The constant coefficient map
proves this is impossible.
-/

namespace ManuscriptAudit.CuspRationalInfinity

open AlgebraicGeometry CategoryTheory
open CuspPunctured CuspProperCompactification

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

private abbrev R := PowerSeries K
private abbrev L := FractionRing (R K)
private abbrev CuspRing := CuspSubalgebra K

private abbrev uniformizer : R K := PowerSeries.X

private abbrev genericParameter : L K :=
  (algebraMap (R K) (L K) (uniformizer K))⁻¹

private def genericEvaluation : CuspRing K →ₐ[K] L K :=
  (Polynomial.aeval (genericParameter K)).comp (CuspSubalgebra K).val

private lemma genericEvaluation_square :
    genericEvaluation K (cuspSquare K) = genericParameter K ^ 2 := by
  change (Polynomial.aeval (genericParameter K) : Polynomial K →ₐ[K] L K)
    ((Polynomial.X : Polynomial K) ^ 2) = _
  rw [map_pow, Polynomial.aeval_X]

private def genericInclusion : Spec (CommRingCat.of (L K)) ⟶ Spec (CommRingCat.of (R K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (R K) (L K)))

private def arcToBase : Spec (CommRingCat.of (R K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (R K)))

private def genericArc : Spec (CommRingCat.of (L K)) ⟶ projectiveCusp K :=
  Spec.map (CommRingCat.ofHom (genericEvaluation K).toRingHom) ≫ affineOpen K

private def arcSquare : ValuativeCommSq (projectiveCuspToBase K) where
  R := R K
  K := L K
  i₁ := genericArc K
  i₂ := arcToBase K
  commSq := ⟨by
    unfold genericArc arcToBase
    simp only [Category.assoc, affineOpen_toBase, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change genericEvaluation K (algebraMap K (CuspRing K) a) =
      algebraMap (R K) (L K) (algebraMap K (R K) a)
    rw [(genericEvaluation K).commutes, IsScalarTower.algebraMap_apply K (R K) (L K)]⟩

private theorem arcSquare_hasLift : (arcSquare K).commSq.HasLift := by
  letI := projectiveCusp_isProper K
  have hClosed : UniversallyClosed (projectiveCuspToBase K) := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hClosed
  exact hClosed.1 (arcSquare K)

private def extendedArc : Spec (CommRingCat.of (R K)) ⟶ projectiveCusp K :=
  letI := arcSquare_hasLift K
  (arcSquare K).commSq.lift

private theorem extendedArc_generic :
    genericInclusion K ≫ extendedArc K = genericArc K := by
  letI := arcSquare_hasLift K
  exact (arcSquare K).commSq.fac_left

private theorem extendedArc_overBase :
    extendedArc K ≫ projectiveCuspToBase K = arcToBase K := by
  letI := arcSquare_hasLift K
  exact (arcSquare K).commSq.fac_right

private def specialInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (R K)) :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

private theorem specialInclusion_closedPoint :
    specialInclusion K (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint (R K) := by
  letI : IsLocalHom (PowerSeries.constantCoeff (R := K)) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact IsLocalRing.Spec_closedPoint

/-- The specialization of the cusp parameter \(t=s^{-1}\) at \(s=0\). -/
def infinityPoint : Spec (CommRingCat.of K) ⟶ projectiveCusp K :=
  specialInclusion K ≫ extendedArc K

/-- The infinity point is a rational point over the original base field. -/
theorem infinityPoint_overBase :
    infinityPoint K ≫ projectiveCuspToBase K = 𝟙 (Spec (CommRingCat.of K)) := by
  unfold infinityPoint
  rw [Category.assoc, extendedArc_overBase]
  unfold specialInclusion arcToBase
  rw [← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change PowerSeries.constantCoeff (algebraMap K (R K) a) = a
  simp [R, PowerSeries.algebraMap_apply]

/-- The rational infinity point defines a closed subscheme of the proper cusp. -/
theorem infinityPoint_isClosedImmersion : IsClosedImmersion (infinityPoint K) := by
  letI := projectiveCusp_isProper K
  haveI : IsClosedImmersion (infinityPoint K ≫ projectiveCuspToBase K) := by
    rw [infinityPoint_overBase]
    infer_instance
  exact IsClosedImmersion.of_comp (infinityPoint K) (projectiveCuspToBase K)

private theorem generic_square_no_regular_lift (r : R K) :
    algebraMap (R K) (L K) r ≠ genericParameter K ^ 2 := by
  intro h
  have hx : algebraMap (R K) (L K) (uniformizer K) ≠ 0 :=
    fun hzero => PowerSeries.X_ne_zero ((IsFractionRing.injective (R K) (L K))
      (hzero.trans (map_zero _).symm))
  have he : algebraMap (R K) (L K) (uniformizer K ^ 2 * r) =
      algebraMap (R K) (L K) 1 := by
    rw [map_mul, map_pow, h, map_one]
    change (algebraMap (R K) (L K) (uniformizer K)) ^ 2 *
      ((algebraMap (R K) (L K) (uniformizer K))⁻¹) ^ 2 = 1
    rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
  have hr : uniformizer K ^ 2 * r = 1 := (IsFractionRing.injective (R K) (L K)) he
  have hc := congrArg (PowerSeries.constantCoeff (R := K)) hr
  simp [uniformizer] at hc

private theorem extendedArc_closedPoint_outside :
    extendedArc K (IsLocalRing.closedPoint (R K)) ∉ Set.range (affineOpen K) := by
  intro hx
  letI := affineOpen_isOpenImmersion K
  let V := (extendedArc K) ⁻¹ᵁ (affineOpen K).opensRange
  have hClosed : IsLocalRing.closedPoint (R K) ∈ V := hx
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hClosed
  have hRange : Set.range (extendedArc K) ⊆ Set.range (affineOpen K) := by
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ V := by rw [hV]; trivial
    exact hp
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (affineOpen K) (extendedArc K) hRange)
  have hGeneric : genericInclusion K ≫ Spec.map g =
      Spec.map (CommRingCat.ofHom (genericEvaluation K).toRingHom) := by
    apply (cancel_mono (affineOpen K)).mp
    calc
      (genericInclusion K ≫ Spec.map g) ≫ affineOpen K =
          genericInclusion K ≫ extendedArc K := by
        simp only [Category.assoc, hg, IsOpenImmersion.lift_fac]
      _ = _ := extendedArc_generic K
  have hRing : g ≫ CommRingCat.ofHom (algebraMap (R K) (L K)) =
      CommRingCat.ofHom (genericEvaluation K).toRingHom :=
    Spec.map_injective (by simpa only [Spec.map_comp, genericInclusion] using hGeneric)
  have hSquare := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hRing) (cuspSquare K)
  change algebraMap (R K) (L K) (g.hom (cuspSquare K)) =
    genericEvaluation K (cuspSquare K) at hSquare
  exact generic_square_no_regular_lift K _ (hSquare.trans (genericEvaluation_square K))

theorem infinityPoint_outside :
    infinityPoint K (IsLocalRing.closedPoint K) ∉ Set.range (affineOpen K) := by
  change extendedArc K (specialInclusion K (IsLocalRing.closedPoint K)) ∉ _
  rw [specialInclusion_closedPoint]
  exact extendedArc_closedPoint_outside K

/-- The rational infinity point does not factor through the affine open. -/
theorem infinityPoint_not_factors :
    ¬ ∃ t : Spec (CommRingCat.of K) ⟶ affineCusp K, t ≫ affineOpen K = infinityPoint K := by
  rintro ⟨t, ht⟩
  apply infinityPoint_outside K
  refine ⟨t (IsLocalRing.closedPoint K), ?_⟩
  change (t ≫ affineOpen K) (IsLocalRing.closedPoint K) =
    infinityPoint K (IsLocalRing.closedPoint K)
  rw [ht]

end

end ManuscriptAudit.CuspRationalInfinity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspRationalInfinity.infinityPoint_overBase,
      ``ManuscriptAudit.CuspRationalInfinity.infinityPoint_isClosedImmersion,
      ``ManuscriptAudit.CuspRationalInfinity.infinityPoint_outside,
      ``ManuscriptAudit.CuspRationalInfinity.infinityPoint_not_factors] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
