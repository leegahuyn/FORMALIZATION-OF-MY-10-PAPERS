import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluing
import PrimalitySheafVerification.ManuscriptAudit.NodalChartCoefficientMaps

/-! The displayed overlap transition is natural for changing the
coefficient ring. The overlap is itself carried to a scheme pullback. -/

namespace ManuscriptAudit.NodalOverlapCoefficientMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalIntegralGluing NodalIntegralChartTransition NodalChartCoefficientMaps

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem overlap_away_mapped :
    IsLocalization.Away (zRingMap R S (yZ R)) (zOverlap S) := by
  rw [zRingMap_y]
  infer_instance

def overlapRingMap : zOverlap R →+* zOverlap S := by
  letI := overlap_away_mapped R S
  exact IsLocalization.Away.map _ _ (zRingMap R S) (yZ R)

theorem overlapRingMap_algebraMap (a : zChart R) :
    overlapRingMap R S (algebraMap (zChart R) (zOverlap R) a) =
      algebraMap (zChart S) (zOverlap S) (zRingMap R S a) := by
  letI := overlap_away_mapped R S
  unfold overlapRingMap IsLocalization.Away.map
  rw [IsLocalization.map_eq]

private theorem overlapRingMap_x : overlapRingMap R S (xZO R) = xZO S := by
  rw [xZO, overlapRingMap_algebraMap, zRingMap_x]
  rfl

private theorem overlapRingMap_y : overlapRingMap R S (yZO R) = yZO S := by
  rw [yZO, overlapRingMap_algebraMap, zRingMap_y]
  rfl

private theorem overlapRingMap_inv : overlapRingMap R S (yZOinv R) = yZOinv S := by
  have hx : yZO R * yZOinv R = 1 :=
    IsLocalization.Away.mul_invSelf (yZ R)
  have hs : yZO S * yZOinv S = 1 :=
    IsLocalization.Away.mul_invSelf (yZ S)
  have h := congrArg (overlapRingMap R S) hx
  rw [map_mul, map_one, overlapRingMap_y] at h
  calc
    _ = (yZOinv S * yZO S) * overlapRingMap R S (yZOinv R) := by
      rw [mul_comm (yZOinv S), hs, one_mul]
    _ = _ := by rw [mul_assoc, h, mul_one]

private theorem overlapRingMap_coeff (a : R) :
    overlapRingMap R S (algebraMap R (zOverlap R) a) =
      algebraMap S (zOverlap S) (algebraMap R S a) := by
  rw [IsScalarTower.algebraMap_apply R (zChart R) (zOverlap R),
    overlapRingMap_algebraMap, zRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (zChart S) (zOverlap S)]

private theorem plane_ringHom_ext {p : Polynomial (Polynomial R)} {T : Type u} [CommRing T]
    {f g : AdjoinRoot p →+* T}
    (hC : ∀ r : R, f (AdjoinRoot.of p (C r)) = g (AdjoinRoot.of p (C r)))
    (hX : f (AdjoinRoot.of p X) = g (AdjoinRoot.of p X))
    (hY : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  refine AdjoinRoot.ringHom_ext ?_ hY
  apply RingHom.ext
  intro a
  induction a using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (hC r) (congrArg (· ^ n) hX)

private theorem yInZ_natural :
    (overlapRingMap R S).comp (yInZ R).toRingHom =
      (yInZ S).toRingHom.comp (yRingMap R S) := by
  refine plane_ringHom_ext R ?_ ?_ ?_
  · intro r
    change overlapRingMap R S (yInZ R (algebraMap R (yChart R) r)) =
      yInZ S (yRingMap R S (algebraMap R (yChart R) r))
    rw [(yInZ R).commutes, overlapRingMap_coeff, yRingMap_algebraMap, (yInZ S).commutes]
  · change overlapRingMap R S (yInZ R (xY R)) = yInZ S (yRingMap R S (xY R))
    rw [yInZ_x, map_mul, overlapRingMap_x, overlapRingMap_inv, yRingMap_x, yInZ_x]
  · change overlapRingMap R S (yInZ R (zY R)) = yInZ S (yRingMap R S (zY R))
    rw [yInZ_z, overlapRingMap_inv, yRingMap_z, yInZ_z]

def overlapMap : overlapScheme S ⟶ overlapScheme R :=
  Spec.map (CommRingCat.ofHom (overlapRingMap R S))
def zMap : zScheme S ⟶ zScheme R :=
  Spec.map (CommRingCat.ofHom (zRingMap R S))
def yMap : yScheme S ⟶ yScheme R :=
  Spec.map (CommRingCat.ofHom (yRingMap R S))

theorem overlapToZ_natural :
    overlapMap R S ≫ overlapToZ R = overlapToZ S ≫ zMap R S := by
  unfold overlapMap overlapToZ zMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact overlapRingMap_algebraMap R S

theorem overlapToY_natural :
    overlapMap R S ≫ overlapToY R = overlapToY S ≫ yMap R S := by
  change Spec.map (CommRingCat.ofHom (overlapRingMap R S)) ≫
      (Spec.map (CommRingCat.ofHom (yToZ R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (yChart R) (yOverlap R)))) =
    (Spec.map (CommRingCat.ofHom (yToZ S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (yChart S) (yOverlap S)))) ≫
      Spec.map (CommRingCat.ofHom (yRingMap R S))
  simp only [Category.assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change overlapRingMap R S
    (yToZ R (algebraMap (yChart R) (yOverlap R) a)) =
      yToZ S (algebraMap (yChart S) (yOverlap S) (yRingMap R S a))
  rw [yToZ_algebraMap, yToZ_algebraMap]
  exact DFunLike.congr_fun (yInZ_natural R S) a

private theorem range_pullback :
    Set.range (overlapToZ S) = Set.range (pullback.fst (zMap R S) (overlapToZ R)) := by
  rw [IsOpenImmersion.range_pullbackFst]
  change Set.range (PrimeSpectrum.comap (algebraMap (zChart S) (zOverlap S))) =
    (PrimeSpectrum.comap (zRingMap R S)) ⁻¹'
      Set.range (PrimeSpectrum.comap (algebraMap (zChart R) (zOverlap R)))
  rw [PrimeSpectrum.localization_away_comap_range (zOverlap S) (yZ S),
    PrimeSpectrum.localization_away_comap_range (zOverlap R) (yZ R)]
  ext a
  change (yZ S ∉ a.asIdeal) ↔ zRingMap R S (yZ R) ∉ a.asIdeal
  rw [zRingMap_y]

/-- Base change carries the actual overlap inclusion into the Z chart
to the corresponding overlap in the changed scheme. -/
theorem overlap_square_isPullback :
    IsPullback (overlapToZ S) (overlapMap R S) (zMap R S) (overlapToZ R) := by
  let e := IsOpenImmersion.isoOfRangeEq (overlapToZ S)
    (pullback.fst (zMap R S) (overlapToZ R)) (range_pullback R S)
  have hF : e.hom ≫ pullback.fst (zMap R S) (overlapToZ R) = overlapToZ S :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hS : e.hom ≫ pullback.snd (zMap R S) (overlapToZ R) = overlapMap R S := by
    apply (cancel_mono (overlapToZ R)).mp
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hF, overlapToZ_natural]
  exact IsPullback.of_iso_pullback ⟨(overlapToZ_natural R S).symm⟩ e hF hS

end
end ManuscriptAudit.NodalOverlapCoefficientMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalOverlapCoefficientMap.overlapToZ_natural,
      ``ManuscriptAudit.NodalOverlapCoefficientMap.overlapToY_natural,
      ``ManuscriptAudit.NodalOverlapCoefficientMap.overlap_square_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
