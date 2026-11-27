import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHOne
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspGeometricFiber
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricEuler
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionIsoDomain

/-! Native compact degree one of the actual geometric pullbacks of the fixed
integral cusp and its relative smooth open. -/

namespace ManuscriptAudit.IntegralCuspNativeCompactHOne

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField)
open IntegralCuspGeometricFiber (geometricFiber geometricSmoothOpen affineIso affineCompactOpen
  smoothCompactOpen smoothPunctureIso smoothCompactOpen_fac)
open NativeSingularCurveCompactHOne (compact cusp_affine_subsingleton)
open CuspNativeCompactSmoothHOne (smoothOpen smoothHOneEquiv)
open ProetaleOpenExtensionIsoDomain (extensionConstantIsoOfSourceIso extensionCongr)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (d : ℕ) [NeZero (d : closureField p)]

/-- The literal geometric affine cusp has no native compact degree-one classes. -/
theorem affine_subsingleton : Subsingleton (compact d (affineCompactOpen p)) := by
  let K := closureField p
  let j := CuspProperCompactification.affineOpen K
  let e := extensionConstantIsoOfSourceIso (affineIso p) j (ZMod d)
  letI := cusp_affine_subsingleton K d
  exact (cohomologyIso (X := CuspProperCompactification.projectiveCusp K) e 1).injective.subsingleton

/-- Its literal relative smooth open has one copy of the finite coefficient group. -/
def smoothEquiv : compact d (smoothCompactOpen p) ≃+ ZMod d := by
  let K := closureField p
  let j := smoothOpen K
  let e := smoothPunctureIso p
  let h : smoothCompactOpen p = e.hom ≫ j := smoothCompactOpen_fac p
  let F := constant (geometricSmoothOpen p).toScheme (ZMod d)
  let f := (extensionCongr (smoothCompactOpen p) (e.hom ≫ j) h).app F
  let g := extensionConstantIsoOfSourceIso e j (ZMod d)
  exact (cohomologyIso (X := CuspProperCompactification.projectiveCusp K) (f ≪≫ g) 1).trans
    (smoothHOneEquiv K d)

omit [NeZero (d : closureField p)] in
/-- Across the literal integral family, the ℓ-power compact groups in degree one
are zero for the affine cusp and cyclic for the smooth open, when ℓ is invertible. -/
theorem primePower (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (r : ℕ) :
    Subsingleton (compact (ℓ ^ r) (affineCompactOpen p)) ∧
      Nonempty (compact (ℓ ^ r) (smoothCompactOpen p) ≃+ ZMod (ℓ ^ r)) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero r (IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp)⟩
  exact ⟨affine_subsingleton p (ℓ ^ r), ⟨smoothEquiv p (ℓ ^ r)⟩⟩

end
end ManuscriptAudit.IntegralCuspNativeCompactHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNativeCompactHOne.affine_subsingleton,
      ``ManuscriptAudit.IntegralCuspNativeCompactHOne.smoothEquiv,
      ``ManuscriptAudit.IntegralCuspNativeCompactHOne.primePower] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
