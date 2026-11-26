import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersection

/-!
# The two restriction maps of the cusp chart intersection

With the Laurent coordinate taken from the infinity chart, the map to
the cusp uses the inverse Laurent coordinate. The two maps to the
charts are the actual projections of the scheme pullback.
-/

namespace ManuscriptAudit.CuspChartIntersectionMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification CuspProperYChart CuspYChartAlgebra
open CuspYChartOverlapAlgebra CuspChartIntersection

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000

universe u

variable (K : Type u) [Field K]

private def laurentInversion :
    Spec (CommRingCat.of (LaurentRing K)) ⟶ Spec (CommRingCat.of (LaurentRing K)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingHom)

/-- In the Laurent coordinate of the infinity chart, the map to the affine
cusp sends the cusp coordinates to the inverse square and inverse cube. -/
def laurentToAffineCusp : Spec (CommRingCat.of (LaurentRing K)) ⟶ affineCusp K :=
  laurentInversion K ≫ CuspYChartImage.laurentToCusp K

private theorem laurentInversion_toLine :
    laurentInversion K ≫ CuspYChartImage.laurentToLine K = laurentToAffineLine K := by
  unfold laurentInversion CuspYChartImage.laurentToLine laurentToAffineLine
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact LaurentPolynomial.involutive_invert (Polynomial.toLaurent f)

/-- The actual Laurent maps agree on the projective cusp. -/
theorem laurent_maps_commute :
    laurentToAffineCusp K ≫ affineOpen K = laurentToAffineLine K ≫ lineOpen K := by
  apply (cancel_mono ((cuspInPlane K).imageι)).mp
  calc
    (laurentToAffineCusp K ≫ affineOpen K) ≫ (cuspInPlane K).imageι =
        laurentInversion K ≫ (CuspYChartImage.laurentToCusp K ≫ cuspInPlane K) := by
      simp only [laurentToAffineCusp, Category.assoc, affineOpen, Scheme.Hom.toImage_imageι]
    _ = laurentInversion K ≫ (CuspYChartImage.laurentToLine K ≫ lineInPlane K) :=
      congrArg (fun f => laurentInversion K ≫ f) (CuspYChartImage.laurentPlane_eq K)
    _ = (laurentToAffineLine K ≫ lineOpen K) ≫ (cuspInPlane K).imageι := by
      rw [← Category.assoc, laurentInversion_toLine, Category.assoc, lineOpen_inPlane]

@[reassoc]
theorem overlapIsoLaurent_inv_toAffineLine :
    (overlapIsoLaurent K).inv ≫ pullback.snd (affineOpen K) (lineOpen K) =
      laurentToAffineLine K := by
  rw [← overlapIsoLaurent_hom_toAffineLine, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc]
theorem overlapIsoLaurent_inv_toAffineCusp :
    (overlapIsoLaurent K).inv ≫ pullback.fst (affineOpen K) (lineOpen K) =
      laurentToAffineCusp K := by
  apply (cancel_mono (affineOpen K)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, overlapIsoLaurent_inv_toAffineLine]
  exact (laurent_maps_commute K).symm

end

end ManuscriptAudit.CuspChartIntersectionMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspChartIntersectionMaps.laurent_maps_commute,
      ``ManuscriptAudit.CuspChartIntersectionMaps.overlapIsoLaurent_inv_toAffineLine,
      ``ManuscriptAudit.CuspChartIntersectionMaps.overlapIsoLaurent_inv_toAffineCusp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
