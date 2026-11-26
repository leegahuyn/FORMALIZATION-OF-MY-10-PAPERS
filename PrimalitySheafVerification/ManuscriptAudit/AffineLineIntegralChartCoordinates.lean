import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorChartSections

/-!
# Canonical algebra coordinates for integral affine étale objects

An arbitrary object of the native affine site is canonically isomorphic
to the actual affine chart of its coordinate ring, endowed with its
native algebra structure over the base.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (U : (X K).AffineEtale)

/-- The coordinate ring of an actual affine étale object. -/
abbrev coordinateRing : CommRingCat.{0} := unop U.left

private abbrev coordinateHom : CommRingCat.of (Polynomial K) ⟶ coordinateRing K U :=
  Spec.preimage U.hom

/-- The structure map of an affine étale chart yields its canonical base algebra. -/
def coordinateAlgebra : Algebra (Polynomial K) (coordinateRing K U) :=
  (coordinateHom K U).hom.toAlgebra

/-- The above coordinate algebra is indeed étale. -/
theorem coordinateAlgebra_etale :
    letI := coordinateAlgebra K U
    Algebra.Etale (Polynomial K) (coordinateRing K U) := by
  let a := coordinateHom K U
  have ha : Spec.map a = U.hom := Spec.map_preimage U.hom
  have h : Etale (Spec.map a) := ha.symm ▸ U.prop
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp h)

/-- The actual chart of the coordinate algebra identifies with the
original integral affine étale object. -/
def coordinateChartIso (hU : IsDomain (coordinateRing K U)) :
    letI := coordinateAlgebra K U
    letI := coordinateAlgebra_etale K U
    letI := hU
    chartObject K (coordinateRing K U) ≅ U := by
  letI := coordinateAlgebra K U
  letI := coordinateAlgebra_etale K U
  letI := hU
  refine MorphismProperty.CostructuredArrow.isoMk (Iso.refl U.left) trivial trivial ?_
  change Spec.map (𝟙 (coordinateRing K U)) ≫ U.hom =
    Spec.map (CommRingCat.ofHom (coordinateHom K U).hom)
  rw [Spec.map_id, Category.id_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.coordinateAlgebra_etale,
      ``ManuscriptAudit.AffineLineDivisorSheaf.coordinateChartIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
