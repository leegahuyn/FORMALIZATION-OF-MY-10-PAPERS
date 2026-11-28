import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricIntegralChartCoordinates
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainSite
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap

/-! The true affine terminal object's chosen coordinate structure is the
original base algebra, with identity structure map on the literal ring. -/

namespace ManuscriptAudit.AffineEtaleIntegralTerminal

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleTensorOverlap AffineGeometricIntegralChartCoordinates

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsDomain A]

/-- The native terminal object in the basis of integral affine étale charts. -/
def integralTerminal : (AffineEtaleDomainSite.integralCharts A).FullSubcategory :=
  ⟨baseObject A, inferInstanceAs (IsDomain A)⟩

/-- The actual base-to-coordinate ring map at the terminal object is the identity. -/
theorem terminal_algebraMap (a : A) :
    letI := coordinateAlgebra A (baseObject A)
    algebraMap A (coordinateRing A (baseObject A)) a = a := by
  let r : CommRingCat.{0} := CommRingCat.of A
  change (Spec.preimage (𝟙 (Spec r))).hom a = a
  rw [← Spec.map_id r, Spec.preimage_map]
  rfl

/-- The actual selected coordinate map is bijective. -/
theorem terminal_algebraMap_bijective :
    letI := coordinateAlgebra A (baseObject A)
    Function.Bijective (algebraMap A (coordinateRing A (baseObject A))) := by
  letI := coordinateAlgebra A (baseObject A)
  have h : (algebraMap A (coordinateRing A (baseObject A)) : A → A) = id :=
    funext (terminal_algebraMap A)
  rw [h]
  exact Function.bijective_id

end

end ManuscriptAudit.AffineEtaleIntegralTerminal

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleIntegralTerminal.terminal_algebraMap_bijective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
