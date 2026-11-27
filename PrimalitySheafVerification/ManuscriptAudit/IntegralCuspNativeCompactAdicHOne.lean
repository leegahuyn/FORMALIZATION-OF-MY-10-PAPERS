import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactAffineAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousExtensionIsoDomain
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNativeCompactHOne

/-! Native continuous compact adic degree one on the literal fibers of
the fixed integral cusp is zero on the cusp and one copy of the adic
integers on the actual smooth open. -/

namespace ManuscriptAudit.IntegralCuspNativeCompactAdicHOne

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField)
open IntegralCuspGeometricFiber (geometricSmoothOpen affineIso affineCompactOpen smoothCompactOpen
  smoothPunctureIso smoothCompactOpen_fac)
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspNativeCompactSmoothHOne (smoothOpen)
open ProetaleContinuousExtensionIsoDomain (extensionFunctionsIsoOfSourceIso)
open ProetaleOpenExtensionIsoDomain (extensionCongr)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

abbrev compactHOne {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (ℓ : ℕ) [Fact ℓ.Prime] :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (functions ℤ_[ℓ] U)) 1

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hp : ℓ ≠ p)

include hp in
theorem affine_subsingleton : Subsingleton (compactHOne (affineCompactOpen p) ℓ) := by
  let K := closureField p
  letI : NeZero (ℓ : K) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  let e := extensionFunctionsIsoOfSourceIso (affineIso p) (affineOpen K) ℤ_[ℓ]
  letI := CuspNativeCompactAffineAdicHOne.compact_HOne_subsingleton K ℓ
  exact (cohomologyIso (X := projectiveCusp K) e 1).injective.subsingleton

def smoothEquiv : compactHOne (smoothCompactOpen p) ℓ ≃+ ℤ_[ℓ] := by
  let K := closureField p
  letI : NeZero (ℓ : K) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  let e := smoothPunctureIso p
  let j := smoothOpen K
  let F := functions ℤ_[ℓ] (geometricSmoothOpen p).toScheme
  let q := (extensionCongr (smoothCompactOpen p) (e.hom ≫ j) (smoothCompactOpen_fac p)).app F
  let t := extensionFunctionsIsoOfSourceIso e j ℤ_[ℓ]
  exact (cohomologyIso (X := projectiveCusp K) (q ≪≫ t) 1).trans
    (CuspNativeCompactSmoothAdicHOne.compactHOneEquiv K ℓ)

end

end ManuscriptAudit.IntegralCuspNativeCompactAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNativeCompactAdicHOne.affine_subsingleton,
      ``ManuscriptAudit.IntegralCuspNativeCompactAdicHOne.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
