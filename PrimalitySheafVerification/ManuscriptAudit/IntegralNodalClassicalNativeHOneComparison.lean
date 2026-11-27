import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalClassicalAdicCohomology
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalEtaleProetaleFiniteHOne
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalNativeCompatibleHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleIdentityTowerComparison

/-! The degree-one comparison between the actual classical section-tower model
and native pro-étale cohomology, through the canonical finite comparisons. -/

namespace ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalTowerExactness (difference_at_odd difference_at_two)
open OpenEtaleSectionTower (sectionsFiber)
open OpenEtaleSectionTowerComparison (positiveEquiv)
open OpenEtaleIdentityTowerComparison (compatibleEquiv levelEquiv)
open ProetaleAdicHOneDetection (reductionMap reductionMap_injective)
open EtaleProetaleCompatibleHOne (comparisonEquiv)
open EtaleProetaleFiniteHOneComparison (comparison)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section General

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]
variable (differenceOnto : Function.Surjective (OpenEtaleTowerDifference.difference (𝟙 X) ℓ 0))
variable (finiteOnto : ∀ r, Function.Surjective (comparison X ℓ r))
variable (nativeOnto : Function.Surjective (reductionMap X ℓ))

private def finiteComparison :=
  ((positiveEquiv (𝟙 X) ℓ 0 differenceOnto).trans (compatibleEquiv X ℓ)).trans
    (comparisonEquiv X ℓ finiteOnto)

private def nativeReduction :=
  AddEquiv.ofBijective (reductionMap X ℓ) ⟨reductionMap_injective X ℓ, nativeOnto⟩

/-- When the actual finite site maps and native reduction are onto, they identify
the degree-one section-tower group with native pro-étale adic cohomology. -/
def fromClassical : (sectionsFiber (𝟙 X) ℓ).homology 1 ≃+ X.EllAdicCohomology ℓ 1 :=
  (finiteComparison X ℓ differenceOnto finiteOnto).trans (nativeReduction X ℓ nativeOnto).symm

/-- The degree-one comparison induces exactly the finite site comparison at every residue order. -/
theorem fromClassical_reduction_apply (x : (sectionsFiber (𝟙 X) ℓ).homology 1) (r : ℕ) :
    (reductionMap X ℓ (fromClassical X ℓ differenceOnto finiteOnto nativeOnto x)).val r =
      comparison X ℓ r
        (levelEquiv X ℓ r ((positiveEquiv (𝟙 X) ℓ 0 differenceOnto x).val r)) := by
  let E := nativeReduction X ℓ nativeOnto
  let y := finiteComparison X ℓ differenceOnto finiteOnto x
  exact congrArg (fun z ↦ z.val r) (E.apply_symm_apply y)

end General

/-- The actual degree-one comparison for the literal proper geometric fibre at (2). -/
def properAtTwo (ℓ : ℕ) [Fact ℓ.Prime] (hℓ₂ : ℓ ≠ 2) :
    IntegralNodalClassicalAdicCohomology.proper ℓ 2 1 ≃+ (geometricFiber 2).EllAdicCohomology ℓ 1 :=
  fromClassical (geometricFiber 2) ℓ
    (difference_at_two ℓ hℓ₂ 0).1
    (fun r ↦ (IntegralNodalEtaleProetaleFiniteHOne.properAtTwo ℓ hℓ₂ r).surjective)
    (IntegralNodalNativeCompatibleHOne.properAtTwo ℓ hℓ₂).surjective

/-- The actual degree-one comparison for every literal proper geometric odd fibre. -/
def properAtOdd (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) :
    IntegralNodalClassicalAdicCohomology.proper ℓ p 1 ≃+ (geometricFiber p).EllAdicCohomology ℓ 1 :=
  fromClassical (geometricFiber p) ℓ
    (difference_at_odd ℓ p hp hℓp 0).1
    (fun r ↦ (IntegralNodalEtaleProetaleFiniteHOne.properAtOdd p ℓ hp hℓp r).surjective)
    (IntegralNodalNativeCompatibleHOne.properAtOdd p ℓ hp hℓp).surjective

end
end ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison.fromClassical,
      ``ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison.fromClassical_reduction_apply,
      ``ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison.properAtTwo,
      ``ManuscriptAudit.IntegralNodalClassicalNativeHOneComparison.properAtOdd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
