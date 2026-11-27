import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalChartPoints
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluingOverlap
import PrimalitySheafVerification.ManuscriptAudit.NodalValuationCoordinates

/-! A valuative lift for the actual integral nodal model, starting
from a field-valued point in the Z chart. -/

namespace ManuscriptAudit.NodalValuationZLift

open AlgebraicGeometry CategoryTheory
open NodalIntegralChartTransition NodalIntegralGluing NodalIntegralGluingOverlap
open NodalChartPoints

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

universe u
variable (R : Type u) [CommRing R] {V K : Type u}
  [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

def inFractionField : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V K))

private def zLocalized (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    zOverlap R →+* K :=
  IsLocalization.Away.lift (g := f) (yZ R) (isUnit_iff_ne_zero.mpr h)

private theorem zLocalized_map (f : zChart R →+* K) (h : f (yZ R) ≠ 0) (a : zChart R) :
    zLocalized R f h (algebraMap (zChart R) (zOverlap R) a) = f a :=
  IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr h) _

private theorem zLocalized_inv (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    zLocalized R f h (yZOinv R) = (f (yZ R))⁻¹ := by
  have hp := congrArg (zLocalized R f h)
    (IsLocalization.Away.mul_invSelf (S := zOverlap R) (yZ R))
  simp only [map_mul, map_one, zLocalized_map] at hp
  exact mul_left_cancel₀ h (hp.trans (mul_inv_cancel₀ h).symm)

private def zAsY (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    yChart R →+* K :=
  (zLocalized R f h).comp (yInZ R).toRingHom

private theorem zAsY_x (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    zAsY R f h (xY R) = f (xZ R) / f (yZ R) := by
  change zLocalized R f h (yInZ R (xY R)) = _
  rw [yInZ_x, map_mul, xZO, zLocalized_map, zLocalized_inv, div_eq_mul_inv]

private theorem zAsY_z (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    zAsY R f h (zY R) = (f (yZ R))⁻¹ := by
  change zLocalized R f h (yInZ R (zY R)) = _
  rw [yInZ_z, zLocalized_inv]

private theorem zAsY_coeff (f : zChart R →+* K) (h : f (yZ R) ≠ 0) (a : R) :
    zAsY R f h (algebraMap R (yChart R) a) = f (algebraMap R (zChart R) a) := by
  change zLocalized R f h (yInZ R (algebraMap R (yChart R) a)) = _
  rw [(yInZ R).commutes, IsScalarTower.algebraMap_apply R (zChart R) (zOverlap R),
    zLocalized_map]

private theorem chartsAgree (f : zChart R →+* K) (h : f (yZ R) ≠ 0) :
    Spec.map (CommRingCat.ofHom f) ≫ chartIn R false =
      Spec.map (CommRingCat.ofHom (zAsY R f h)) ≫ chartIn R true := by
  let g := Spec.map (CommRingCat.ofHom (zLocalized R f h))
  have hz : g ≫ overlapToZ R = Spec.map (CommRingCat.ofHom f) := by
    unfold g overlapToZ
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact zLocalized_map R f h
  have hy : g ≫ overlapToY R = Spec.map (CommRingCat.ofHom (zAsY R f h)) := by
    change Spec.map (CommRingCat.ofHom (zLocalized R f h)) ≫
      (Spec.map (CommRingCat.ofHom (yToZ R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (yChart R) (yOverlap R)))) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change zLocalized R f h (yToZ R (algebraMap (yChart R) (yOverlap R) a)) =
      zLocalized R f h (yInZ R a)
    rw [yToZ_algebraMap]
  calc
    _ = g ≫ overlapToZ R ≫ chartIn R false := by rw [← Category.assoc, hz]
    _ = g ≫ overlapToY R ≫ chartIn R true := by rw [overlap_condition]
    _ = _ := by rw [← Category.assoc, hy]

private theorem liftFromZ (c : R →+* V) (f : zChart R →+* K)
    (hc : ∀ a : R, f (algebraMap R (zChart R) a) = algebraMap V K (c a))
    (x y : V) (hx : algebraMap V K x = f (xZ R)) (hy : algebraMap V K y = f (yZ R))
    (he : y ^ 2 = x ^ 2 * (x + 1)) :
    ∃ g : Spec (CommRingCat.of V) ⟶ model R,
      inFractionField ≫ g = Spec.map (CommRingCat.ofHom f) ≫ chartIn R false ∧
      g ≫ toBase R = Spec.map (CommRingCat.ofHom c) := by
  let F := zEval c x y he
  let g := Spec.map (CommRingCat.ofHom F)
  have hg : (algebraMap V K).comp F = f := by
    refine planeHom_ext ?_ ?_ ?_
    · intro a
      change algebraMap V K (F (algebraMap R (zChart R) a)) = _
      rw [zEval_coeff, hc]
    · change algebraMap V K (F (xZ R)) = f (xZ R)
      rw [zEval_x, hx]
    · change algebraMap V K (F (yZ R)) = f (yZ R)
      rw [zEval_y, hy]
  refine ⟨g ≫ chartIn R false, ?_, ?_⟩
  · unfold g inFractionField
    rw [← Category.assoc, ← Spec.map_comp]
    rw [show (CommRingCat.ofHom F) ≫ CommRingCat.ofHom (algebraMap V K) =
      CommRingCat.ofHom f from CommRingCat.hom_ext hg]
  · rw [Category.assoc, chartIn_over]
    change Spec.map (CommRingCat.ofHom F) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (zChart R))) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact zEval_coeff c x y he

theorem liftFromY (c : R →+* V) (f : yChart R →+* K)
    (hc : ∀ a : R, f (algebraMap R (yChart R) a) = algebraMap V K (c a))
    (x z : V) (hx : algebraMap V K x = f (xY R)) (hz : algebraMap V K z = f (zY R))
    (he : z = x ^ 2 * (x + z)) :
    ∃ g : Spec (CommRingCat.of V) ⟶ model R,
      inFractionField ≫ g = Spec.map (CommRingCat.ofHom f) ≫ chartIn R true ∧
      g ≫ toBase R = Spec.map (CommRingCat.ofHom c) := by
  let F := yEval c x z he
  let g := Spec.map (CommRingCat.ofHom F)
  have hg : (algebraMap V K).comp F = f := by
    refine planeHom_ext ?_ ?_ ?_
    · intro a
      change algebraMap V K (F (algebraMap R (yChart R) a)) = _
      rw [yEval_coeff, hc]
    · change algebraMap V K (F (xY R)) = f (xY R)
      rw [yEval_x, hx]
    · change algebraMap V K (F (zY R)) = f (zY R)
      rw [yEval_z, hz]
  refine ⟨g ≫ chartIn R true, ?_, ?_⟩
  · unfold g inFractionField
    rw [← Category.assoc, ← Spec.map_comp]
    rw [show (CommRingCat.ofHom F) ≫ CommRingCat.ofHom (algebraMap V K) =
      CommRingCat.ofHom f from CommRingCat.hom_ext hg]
  · rw [Category.assoc, chartIn_over]
    change Spec.map (CommRingCat.ofHom F) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (yChart R))) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact yEval_coeff c x z he

/-- A field-valued point in the Z chart extends over the valuation ring,
possibly landing in the other chart. -/
theorem lift_zPoint (c : R →+* V) (f : zChart R →+* K)
    (hc : ∀ a : R, f (algebraMap R (zChart R) a) = algebraMap V K (c a)) :
    ∃ g : Spec (CommRingCat.of V) ⟶ model R,
      inFractionField ≫ g = Spec.map (CommRingCat.ofHom f) ≫ chartIn R false ∧
      g ≫ toBase R = Spec.map (CommRingCat.ofHom c) := by
  have he : f (yZ R) ^ 2 = f (xZ R) ^ 2 * (f (xZ R) + 1) := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f (z_relation R)
  rcases NodalValuationCoordinates.valuationRing_coordinates V K he with
    ⟨a, b, ha, hb, hab⟩ | ⟨hn, a, b, ha, hb, hab⟩
  · exact liftFromZ R c f hc a b ha hb hab
  · have hc' : ∀ a : R, zAsY R f hn (algebraMap R (yChart R) a) = algebraMap V K (c a) :=
      fun a => (zAsY_coeff R f hn a).trans (hc a)
    have ha' := ha.trans (zAsY_x R f hn).symm
    have hb' := hb.trans (zAsY_z R f hn).symm
    obtain ⟨g, hg, hbase⟩ := liftFromY R c (zAsY R f hn) hc' a b ha' hb' hab
    exact ⟨g, hg.trans (chartsAgree R f hn).symm, hbase⟩

end
end ManuscriptAudit.NodalValuationZLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalValuationZLift.lift_zPoint
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
