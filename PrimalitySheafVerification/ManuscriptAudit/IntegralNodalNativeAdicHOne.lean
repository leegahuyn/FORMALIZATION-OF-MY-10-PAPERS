import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricEuler
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology

/-! The literal odd geometric fibres of the fixed integral nodal family
have native integral pro-étale H¹ isomorphic to the coefficient group. -/

namespace ManuscriptAudit.IntegralNodalNativeAdicHOne

open AlgebraicGeometry
open IntegralNodalGeometricFiber (closureField geometricFiber projectiveIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Native degree-one integral cohomology of the actual proper odd fibre. -/
def properAtOdd (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) :
    (geometricFiber p).EllAdicCohomology ℓ 1 ≃+ ℤ_[ℓ] := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp⟩
  let h₂ : (2 : closureField p) ≠ 0 := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
  exact (SchemeIsoProetaleCohomology.adicCohomologyEquiv (projectiveIso p) ℓ 1).trans
    (NodalNativeAdicHOne.adicHOneEquiv (closureField p) h₂ ℓ)

end
end ManuscriptAudit.IntegralNodalNativeAdicHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegralNodalNativeAdicHOne.properAtOdd
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
