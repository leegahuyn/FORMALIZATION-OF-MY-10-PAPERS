import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactAffineAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNativeCompactAdicHOne

/-! Actual compact degree-two classes with continuous adic coefficients
on the literal geometric fibers of the fixed integral cusp and its smooth open. -/

namespace ManuscriptAudit.IntegralCuspNativeCompactAdicHTwoLower

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
set_option maxRecDepth 2048

abbrev compactHTwo {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (ℓ : ℕ) [Fact ℓ.Prime] :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (functions ℤ_[ℓ] U)) 2

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]

private def affineEquiv :
    compactHTwo (affineCompactOpen p) ℓ ≃+ compactHTwo (affineOpen (closureField p)) ℓ := by
  let K := closureField p
  let e := extensionFunctionsIsoOfSourceIso (affineIso p) (affineOpen K) ℤ_[ℓ]
  exact cohomologyIso (X := projectiveCusp K) e 2

private def smoothEquiv :
    compactHTwo (smoothCompactOpen p) ℓ ≃+ compactHTwo (smoothOpen (closureField p)) ℓ := by
  let K := closureField p
  let e := smoothPunctureIso p
  let j := smoothOpen K
  let F := functions ℤ_[ℓ] (geometricSmoothOpen p).toScheme
  let q := (extensionCongr (smoothCompactOpen p) (e.hom ≫ j) (smoothCompactOpen_fac p)).app F
  let t := extensionFunctionsIsoOfSourceIso e j ℤ_[ℓ]
  exact cohomologyIso (X := projectiveCusp K) (q ≪≫ t) 2

/-- An actual adic Laurent class on the compactly supported affine cusp of the fixed family. -/
def affineInclusion (hp : ℓ ≠ p) : ℤ_[ℓ] →+ compactHTwo (affineCompactOpen p) ℓ := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  exact (affineEquiv p ℓ).symm.toAddMonoidHom.comp
    (CuspNativeCompactAffineAdicHTwoLower.inclusion (closureField p) ℓ)

theorem affineInclusion_injective (hp : ℓ ≠ p) : Function.Injective (affineInclusion p ℓ hp) := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  intro x y h
  apply CuspNativeCompactAffineAdicHTwoLower.inclusion_injective (closureField p) ℓ
  exact (affineEquiv p ℓ).symm.injective h

/-- The actual adic Laurent class on the compactly supported smooth locus of the fixed family. -/
def smoothInclusion (hp : ℓ ≠ p) : ℤ_[ℓ] →+ compactHTwo (smoothCompactOpen p) ℓ := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  exact (smoothEquiv p ℓ).symm.toAddMonoidHom.comp
    (CuspNativeCompactSmoothAdicHTwoLower.inclusion (closureField p) ℓ)

theorem smoothInclusion_injective (hp : ℓ ≠ p) : Function.Injective (smoothInclusion p ℓ hp) := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hp⟩
  intro x y h
  apply CuspNativeCompactSmoothAdicHTwoLower.inclusion_injective (closureField p) ℓ
  exact (smoothEquiv p ℓ).symm.injective h

end
end ManuscriptAudit.IntegralCuspNativeCompactAdicHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNativeCompactAdicHTwoLower.affineInclusion_injective,
      ``ManuscriptAudit.IntegralCuspNativeCompactAdicHTwoLower.smoothInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
