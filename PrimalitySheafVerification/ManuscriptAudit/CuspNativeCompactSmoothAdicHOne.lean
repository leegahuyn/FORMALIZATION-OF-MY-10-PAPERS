import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicBoundaryPairHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspProperTwoBoundaryPoints
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary

/-! The actual smooth cusp open has native compact continuous adic
cohomology in degree one given by the difference of the two boundary values. -/

namespace ManuscriptAudit.CuspNativeCompactSmoothAdicHOne

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin boundary_disjoint smoothOpen_range smoothOpen_quasiCompact)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

/-- The genuine native compact degree-one group of the actual smooth cusp open. -/
def compactHOneEquiv :
    Sheaf.H ((extensionByZero (smoothOpen K) AddCommGrpCat.{1}).obj (functions ℤ_[ℓ] _)) 1 ≃+ ℤ_[ℓ] := by
  let i₀ := origin K
  let i₁ := infinityPoint K
  let j := smoothOpen K
  letI : IsClosedImmersion i₀ := properOrigin_closed K
  letI : IsClosedImmersion i₁ := infinityPoint_isClosedImmersion K
  letI : QuasiCompact j := smoothOpen_quasiCompact K
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  let a := ProetaleAdicClosedPairSupport.extensionKernelIso i₀ i₁ ℓ j (smoothOpen_range K)
  let b := ProetaleAdicBoundaryPairHOne.supportHOneEquiv K i₀ i₁ ℓ (boundary_disjoint K)
    (CuspNativeProetaleProperHOne.adic_HOne_subsingleton K ℓ)
  exact (cohomologyIso (X := projectiveCusp K) a 1).trans b

end

end ManuscriptAudit.CuspNativeCompactSmoothAdicHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeCompactSmoothAdicHOne.compactHOneEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
