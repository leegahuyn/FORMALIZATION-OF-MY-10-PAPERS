import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicCompatibleHOne
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoNativeAdicReduction
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricEuler

/-! The actual integral native H¹ of the literal proper geometric
fibres agrees with its own compatible finite native residue groups. -/

namespace ManuscriptAudit.IntegralNodalNativeCompatibleHOne

open AlgebraicGeometry
open IntegralNodalGeometricFiber (closureField geometricFiber projectiveIso)
open IntegralNodalCharacteristicTwoGeometry (cuspProjectiveIso coefficientField)
open ProetaleAdicHOneDetection (compatibleHOne reductionMap)
open SchemeIsoNativeAdicReduction (reductionEquivOfIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Native reduction identifies the literal integral group with its compatible residue classes on the proper fibre at (2). -/
def properAtTwo (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2) :
    (geometricFiber 2).EllAdicCohomology ℓ 1 ≃+ compatibleHOne (geometricFiber 2) ℓ := by
  letI : NeZero (ℓ : coefficientField) :=
    ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  exact reductionEquivOfIso cuspProjectiveIso ℓ
    (NativeAdicCompatibleHOne.cuspReductionEquiv coefficientField ℓ).surjective

/-- Native reduction identifies the literal integral group with its compatible residue classes on every proper odd fibre. -/
def properAtOdd (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) :
    (geometricFiber p).EllAdicCohomology ℓ 1 ≃+ compatibleHOne (geometricFiber p) ℓ := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp⟩
  let h₂ : (2 : closureField p) ≠ 0 :=
    IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
  exact reductionEquivOfIso (projectiveIso p) ℓ
    (NativeAdicCompatibleHOne.node_reduction_surjective (closureField p) h₂ ℓ)

theorem properAtTwo_apply (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2)
    (x : (geometricFiber 2).EllAdicCohomology ℓ 1) :
    properAtTwo ℓ hℓ₂ x = reductionMap (geometricFiber 2) ℓ x := rfl

theorem properAtOdd_apply (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p)
    (x : (geometricFiber p).EllAdicCohomology ℓ 1) :
    properAtOdd p ℓ hp hℓp x = reductionMap (geometricFiber p) ℓ x := rfl

end
end ManuscriptAudit.IntegralNodalNativeCompatibleHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalNativeCompatibleHOne.properAtTwo,
      ``ManuscriptAudit.IntegralNodalNativeCompatibleHOne.properAtOdd,
      ``ManuscriptAudit.IntegralNodalNativeCompatibleHOne.properAtTwo_apply,
      ``ManuscriptAudit.IntegralNodalNativeCompatibleHOne.properAtOdd_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
