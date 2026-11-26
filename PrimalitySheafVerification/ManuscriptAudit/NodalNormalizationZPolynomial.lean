import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeNormalizationScheme
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationZChart
import PrimalitySheafVerification.ManuscriptAudit.NodalRelativeNormalization

/-! The actual normalized projective Z-chart is the affine polynomial line. -/

namespace ManuscriptAudit.NodalNormalizationZPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen)
open NodalProjectiveNormalization (normalizationMap)
open NodalNormalizationZChart (punctureNormalizationZIso)
open NodalRelativeNormalization (A L polynomialEquivIntegralClosure)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

/-- The actual Z-chart of the normalized projective node is the affine
parameter line. -/
def normalizationZPolynomialIso (h2 : (2 : K) ≠ 0) :
    pullback (normalizationMap K) (affineOpen K) ≅ Spec (CommRingCat.of (Polynomial K)) :=
  (punctureNormalizationZIso K).symm ≪≫
    AffineRelativeNormalizationScheme.normalizationSpecIso (A K) (L K) ≪≫
    Scheme.Spec.mapIso (polynomialEquivIntegralClosure K h2).toRingEquiv.toCommRingCatIso.op

end
end ManuscriptAudit.NodalNormalizationZPolynomial

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizationZPolynomial.normalizationZPolynomialIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
