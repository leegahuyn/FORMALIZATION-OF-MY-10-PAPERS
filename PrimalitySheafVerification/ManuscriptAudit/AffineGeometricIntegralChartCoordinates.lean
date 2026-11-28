import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorSections

/-!
# Canonical algebra coordinates for integral affine étale objects

An arbitrary object of the native affine site is canonically isomorphic
to the actual affine chart of its coordinate ring, endowed with its
native algebra structure over the base.
-/

namespace ManuscriptAudit.AffineGeometricIntegralChartCoordinates

open AlgebraicGeometry CategoryTheory Opposite
open AffineGeometricDivisorSections AffineGeometricDivisorSheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A]
variable (U : (X A).AffineEtale)

/-- The coordinate ring of an actual affine étale object. -/
abbrev coordinateRing : CommRingCat.{0} := unop U.left

private abbrev coordinateHom : CommRingCat.of A ⟶ coordinateRing A U :=
  Spec.preimage U.hom

/-- The structure map of an affine étale chart yields its canonical base algebra. -/
def coordinateAlgebra : Algebra A (coordinateRing A U) :=
  (coordinateHom A U).hom.toAlgebra

/-- The above coordinate algebra is indeed étale. -/
theorem coordinateAlgebra_etale :
    letI := coordinateAlgebra A U
    Algebra.Etale A (coordinateRing A U) := by
  letI : Algebra A (coordinateRing A U) := coordinateAlgebra A U
  let a := coordinateHom A U
  have ha : Spec.map a = U.hom := Spec.map_preimage U.hom
  have h : Etale (Spec.map a) := ha.symm ▸ U.prop
  have he : (algebraMap A (coordinateRing A U)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp h
  exact RingHom.etale_algebraMap.mp he

/-- The actual chart of the coordinate algebra identifies with the
original integral affine étale object. -/
def coordinateChartIso (hU : IsDomain (coordinateRing A U)) :
    letI := coordinateAlgebra A U
    letI := coordinateAlgebra_etale A U
    letI := hU
    chartObject A (coordinateRing A U) ≅ U := by
  letI := coordinateAlgebra A U
  letI := coordinateAlgebra_etale A U
  letI := hU
  refine MorphismProperty.CostructuredArrow.isoMk (Iso.refl U.left) trivial trivial ?_
  change Spec.map (𝟙 (coordinateRing A U)) ≫ U.hom =
    Spec.map (CommRingCat.ofHom (coordinateHom A U).hom)
  rw [Spec.map_id, Category.id_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

end

end ManuscriptAudit.AffineGeometricIntegralChartCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricIntegralChartCoordinates.coordinateAlgebra_etale,
      ``ManuscriptAudit.AffineGeometricIntegralChartCoordinates.coordinateChartIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
