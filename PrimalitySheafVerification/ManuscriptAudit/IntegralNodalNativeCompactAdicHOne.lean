import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeCompactAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricBoundary
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalNativeAdicHOne

/-! The actual relative smooth locus of the fixed integral nodal family
has compact degree-one cohomology with its literal native adic coefficients. -/

namespace ManuscriptAudit.IntegralNodalNativeCompactAdicHOne

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber geometricToBase geometric_proper)
open IntegralNodalGeometricBoundary (geometricSmoothOpen geometricSmoothIso origin origin_closed
  geometric_smooth_range)
open NodalNativeCompactAdicHOne (compactHOne)
open NodalSmoothLocusOverlap (smoothScheme)
open NodalProjectiveNormalization (smoothInclusion smoothInclusion_quasiCompact)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

private theorem smooth_quasiCompact : QuasiCompact (geometricSmoothOpen p).ι := by
  let K := closureField p
  letI : IsProper (NodalProjectiveClosure.projectiveNodeToBase K) :=
    NodalProjectiveClosure.projectiveNode_isProper K
  letI : CompactSpace (NodalProjectiveClosure.projectiveNode K) :=
    QuasiCompact.compactSpace_of_compactSpace (NodalProjectiveClosure.projectiveNodeToBase K)
  letI : QuasiCompact (smoothInclusion K) := smoothInclusion_quasiCompact K
  letI : CompactSpace (smoothScheme K) := QuasiCompact.compactSpace_of_compactSpace (smoothInclusion K)
  letI : CompactSpace (geometricSmoothOpen p).toScheme :=
    (geometricSmoothIso p).inv.homeomorph.compactSpace
  letI : IsProper (geometricToBase p) := geometric_proper p
  letI : QuasiSeparatedSpace (geometricFiber p) := quasiSeparatedSpace_of_quasiSeparated (geometricToBase p)
  exact quasiCompact_of_compactSpace _

/-- Compact H¹ of the actual geometric smooth locus maps to the ordinary H¹ of its literal compactification. -/
def smoothToProper (ℓ : ℕ) [Fact ℓ.Prime] :
    compactHOne (geometricSmoothOpen p).ι ℓ ≃+ (geometricFiber p).EllAdicCohomology ℓ 1 := by
  letI : IsClosedImmersion (origin p) := origin_closed p
  letI : QuasiCompact (geometricSmoothOpen p).ι := smooth_quasiCompact p
  exact ProetaleAdicOpenClosedHOne.compactHOneEquiv (closureField p) (origin p) ℓ
    (geometricSmoothOpen p).ι (geometric_smooth_range p)

/-- At any odd geometric fibre the actual relative smooth open has compact H¹ isomorphic to the adic integers. -/
def smoothAtOdd (ℓ : ℕ) [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) :
    compactHOne (geometricSmoothOpen p).ι ℓ ≃+ ℤ_[ℓ] :=
  (smoothToProper p ℓ).trans (IntegralNodalNativeAdicHOne.properAtOdd p ℓ hp hℓp)

end
end ManuscriptAudit.IntegralNodalNativeCompactAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalNativeCompactAdicHOne.smoothToProper,
      ``ManuscriptAudit.IntegralNodalNativeCompactAdicHOne.smoothAtOdd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
