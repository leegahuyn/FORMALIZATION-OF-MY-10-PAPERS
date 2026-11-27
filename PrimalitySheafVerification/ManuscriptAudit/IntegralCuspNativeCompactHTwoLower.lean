import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNativeCompactHOne

/-! Native compact degree-two cyclic classes on the literal geometric
pullbacks of the fixed integral cusp and its relative smooth open. -/

namespace ManuscriptAudit.IntegralCuspNativeCompactHTwoLower

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField)
open IntegralCuspGeometricFiber (geometricSmoothOpen affineIso affineCompactOpen
  smoothCompactOpen smoothPunctureIso smoothCompactOpen_fac)
open CuspNativeCompactSmoothHOne (smoothOpen)
open ProetaleOpenExtensionIsoDomain (extensionConstantIsoOfSourceIso extensionCongr)
open OpenProetaleExtension (extensionByZero)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The native cohomology of the actual compactly supported constant coefficient sheaf. -/
abbrev compactHTwo {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ) :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (constant U (ZMod d))) 2

variable (p : ℕ) [Fact p.Prime] (d : ℕ)

private def affineEquiv :
    compactHTwo (affineCompactOpen p) d ≃+
      compactHTwo (CuspProperCompactification.affineOpen (closureField p)) d := by
  let K := closureField p
  let j := CuspProperCompactification.affineOpen K
  let e := extensionConstantIsoOfSourceIso (affineIso p) j (ZMod d)
  exact cohomologyIso (X := CuspProperCompactification.projectiveCusp K) e 2

private def smoothEquiv :
    compactHTwo (smoothCompactOpen p) d ≃+ compactHTwo (smoothOpen (closureField p)) d := by
  let K := closureField p
  let j := smoothOpen K
  let e := smoothPunctureIso p
  let h : smoothCompactOpen p = e.hom ≫ j := smoothCompactOpen_fac p
  let F := constant (geometricSmoothOpen p).toScheme (ZMod d)
  let f := (extensionCongr (smoothCompactOpen p) (e.hom ≫ j) h).app F
  let g := extensionConstantIsoOfSourceIso e j (ZMod d)
  exact cohomologyIso (X := CuspProperCompactification.projectiveCusp K) (f ≪≫ g) 2

variable [NeZero (d : closureField p)]

def affineInclusion : ZMod d →+ compactHTwo (affineCompactOpen p) d :=
  (affineEquiv p d).symm.toAddMonoidHom.comp (CuspNativeCompactHTwoLower.affineInclusion (closureField p) d)

set_option maxRecDepth 2048 in
theorem affineInclusion_injective : Function.Injective (affineInclusion p d) := by
  intro x y h
  apply CuspNativeCompactHTwoLower.affineInclusion_injective (closureField p) d
  exact (affineEquiv p d).symm.injective h

def smoothInclusion : ZMod d →+ compactHTwo (smoothCompactOpen p) d :=
  (smoothEquiv p d).symm.toAddMonoidHom.comp
    (CuspNativeCompactSmoothHTwoLower.smoothInclusion (closureField p) d)

set_option maxRecDepth 2048 in
theorem smoothInclusion_injective : Function.Injective (smoothInclusion p d) := by
  intro x y h
  apply CuspNativeCompactSmoothHTwoLower.smoothInclusion_injective (closureField p) d
  exact (smoothEquiv p d).symm.injective h

omit [NeZero (d : closureField p)] in
/-- Each actual geometric fiber and its relative smooth open have
these native compact degree-two classes at every invertible prime-power order. -/
theorem primePower (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (r : ℕ) :
    (∃ f : ZMod (ℓ ^ r) →+ compactHTwo (affineCompactOpen p) (ℓ ^ r), Function.Injective f) ∧
      (∃ f : ZMod (ℓ ^ r) →+ compactHTwo (smoothCompactOpen p) (ℓ ^ r), Function.Injective f) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero r (IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp)⟩
  exact ⟨⟨affineInclusion p (ℓ ^ r), affineInclusion_injective p (ℓ ^ r)⟩,
    ⟨smoothInclusion p (ℓ ^ r), smoothInclusion_injective p (ℓ ^ r)⟩⟩

end
end ManuscriptAudit.IntegralCuspNativeCompactHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNativeCompactHTwoLower.affineInclusion_injective,
      ``ManuscriptAudit.IntegralCuspNativeCompactHTwoLower.smoothInclusion_injective,
      ``ManuscriptAudit.IntegralCuspNativeCompactHTwoLower.primePower] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
