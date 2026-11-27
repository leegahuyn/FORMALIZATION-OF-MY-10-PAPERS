import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EllAdicHZeroComparison
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalClassicalAdicCohomology

/-! Direct comparison of the two actual adic cohomology models in degree zero on the fixed nodal family. -/

namespace ManuscriptAudit.IntegralNodalAdicZeroComparison

open AlgebraicGeometry
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalClassicalAdicCohomology (proper properAtTwo properAtOdd)
open EllAdicHZeroComparison (properFiberEquiv)

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Classical compact cohomology in degree zero of the literal proper geometric
fibre agrees additively with its actual Mathlib pro-étale ℓ-adic H⁰. -/
def properComparison (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    proper ℓ p 0 ≃+ (geometricFiber p).EllAdicCohomology ℓ 0 := by
  let e := properFiberEquiv ℓ p
  by_cases hp : p = 2
  · subst p
    exact (properAtTwo ℓ hℓp 0 (Or.inl rfl)).trans e.symm
  · have h : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (fun h ↦ hp h.symm)
    exact (properAtOdd ℓ p h hℓp 0 (by decide)).trans e.symm

end
end ManuscriptAudit.IntegralNodalAdicZeroComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegralNodalAdicZeroComparison.properComparison
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
