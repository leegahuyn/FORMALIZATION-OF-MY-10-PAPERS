import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFiniteHOneComparison
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoGeometry
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! The actual degree-one site comparison is bijective with finite
residue coefficients on the literal proper geometric fibres. -/

namespace ManuscriptAudit.IntegralNodalEtaleProetaleFiniteHOne

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber projectiveIso)
open IntegralNodalCharacteristicTwoGeometry (coefficientField cuspProjectiveIso)
open ProetaleAdicHOneDetection (finiteCoefficient)
open EtaleProetaleFiniteHOneComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- The actual native degree-one site map on the literal proper geometric fibre at (2). -/
def properAtTwo (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2) (n : ℕ) :
    Sheaf.H (etaleCoefficient (geometricFiber 2) ℓ n) 1 ≃+
      Sheaf.H (finiteCoefficient (geometricFiber 2) ℓ n) 1 := by
  letI : NeZero (ℓ : coefficientField) :=
    ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  let e := SchemeIsoProetaleCohomology.continuousCohomologyEquiv cuspProjectiveIso (ZMod (ℓ ^ n)) 1
  letI := CuspNativeProetaleProperHOne.residue_HOne_subsingleton coefficientField ℓ n
  have h : Subsingleton (Sheaf.H (finiteCoefficient (geometricFiber 2) ℓ n) 1) :=
    e.injective.subsingleton
  exact AddEquiv.ofBijective (comparison (geometricFiber 2) ℓ n)
    ⟨comparison_injective (geometricFiber 2) ℓ n, fun y ↦ ⟨0, h.elim _ _⟩⟩

/-- The actual native degree-one site map on each literal proper geometric odd fibre. -/
def properAtOdd (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) :
    Sheaf.H (etaleCoefficient (geometricFiber p) ℓ n) 1 ≃+
      Sheaf.H (finiteCoefficient (geometricFiber p) ℓ n) 1 := by
  let K := closureField p
  letI : NeZero (ℓ : K) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp⟩
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (show ℓ ≠ 0 from (Fact.out : Nat.Prime ℓ).ne_zero)⟩
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  let h₂ : (2 : K) ≠ 0 := IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
  let e := SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv (projectiveIso p)
    (AddCommGrpCat.of (ZMod (ℓ ^ n))) 1
  let f := SchemeIsoProetaleCohomology.continuousCohomologyEquiv (projectiveIso p) (ZMod (ℓ ^ n)) 1
  have h : Function.Surjective (comparison (geometricFiber p) ℓ n) :=
    comparison_surjective_of_finiteType (geometricFiber p) ℓ n (ZMod (ℓ ^ n))
      (e.trans (NodalProjectiveCyclicHOne.projectiveHOneEquiv K (ℓ ^ n) h₂)).toEquiv
      (f.trans (NodalNativeConductorHOne.residueHOneEquiv K h₂ ℓ n)).toEquiv
  exact AddEquiv.ofBijective (comparison (geometricFiber p) ℓ n)
    ⟨comparison_injective (geometricFiber p) ℓ n, h⟩

end
end ManuscriptAudit.IntegralNodalEtaleProetaleFiniteHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalEtaleProetaleFiniteHOne.properAtTwo,
      ``ManuscriptAudit.IntegralNodalEtaleProetaleFiniteHOne.properAtOdd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
