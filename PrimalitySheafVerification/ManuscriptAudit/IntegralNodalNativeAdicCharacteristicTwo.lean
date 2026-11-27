import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne

/-! The actual integral nodal geometric fibre at (2) has trivial
native degree-one adic cohomology at each odd coefficient prime. -/

namespace ManuscriptAudit.IntegralNodalNativeAdicCharacteristicTwo

open AlgebraicGeometry
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalCharacteristicTwoGeometry (coefficientField cuspProjectiveIso cuspAffineIso)

noncomputable section

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2)

include hℓ₂

/-- Actual native H¹ of the proper geometric fibre at (2) vanishes. -/
theorem properAtTwo_subsingleton : Subsingleton ((geometricFiber 2).EllAdicCohomology ℓ 1) := by
  letI : NeZero (ℓ : coefficientField) :=
    ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  let e := SchemeIsoProetaleCohomology.adicCohomologyEquiv cuspProjectiveIso ℓ 1
  letI := CuspNativeProetaleProperHOne.adic_HOne_subsingleton coefficientField ℓ
  exact e.injective.subsingleton

/-- Actual native ordinary H¹ of the pulled-back affine chart at (2) also vanishes. -/
theorem affineAtTwo_subsingleton :
    Subsingleton ((IntegralNodalGeometricPrimePower.geometricAffine 2).EllAdicCohomology ℓ 1) := by
  letI : NeZero (ℓ : coefficientField) :=
    ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  let e := SchemeIsoProetaleCohomology.adicCohomologyEquiv cuspAffineIso ℓ 1
  letI := CuspNativeProetaleAffineHOne.adic_HOne_subsingleton coefficientField ℓ
  exact e.injective.subsingleton

end
end ManuscriptAudit.IntegralNodalNativeAdicCharacteristicTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalNativeAdicCharacteristicTwo.properAtTwo_subsingleton,
      ``ManuscriptAudit.IntegralNodalNativeAdicCharacteristicTwo.affineAtTwo_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
