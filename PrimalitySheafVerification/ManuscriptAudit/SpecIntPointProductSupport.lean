import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GenericPointSupportDetection
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientClosureSupport

/-! The independently restricted product over the closed primes also supports a generic germ. -/

namespace ManuscriptAudit.SpecIntPointProductSupport

open Set TopologicalSpace
open PointCoefficientSheaf PointCoefficientClosureSupport ClosedSupportDetection

noncomputable section

abbrev X := TopCat.of (PrimeSpectrum ℤ)

def closedPrimes : Set X := {x | x ≠ (⊥ : PrimeSpectrum ℤ)}

theorem closure_closedPrimes : closure closedPrimes = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases h : x = (⊥ : PrimeSpectrum ℤ)
  · rw [h, mem_closure_iff]
    intro U hOpen hU
    exact GenericPointSupportDetection.specInt_neighborhood_contains_nonzero_prime
      ⟨U, hOpen⟩ hU
  · exact subset_closure h

theorem all_stalks_supported (A : closedPrimes → Type)
    [∀ p : closedPrimes, AddCommGroup (A p)] [∀ p : closedPrimes, Nontrivial (A p)] :
    stalkSupport (sheaf closedPrimes A) = univ :=
  (support_eq_closure closedPrimes A).trans closure_closedPrimes

theorem generic_germ_outside_input (A : closedPrimes → Type)
    [∀ p : closedPrimes, AddCommGroup (A p)] [∀ p : closedPrimes, Nontrivial (A p)] :
    (⊥ : PrimeSpectrum ℤ) ∈ stalkSupport (sheaf closedPrimes A) ∧
      (⊥ : PrimeSpectrum ℤ) ∉ closedPrimes := by
  rw [all_stalks_supported A]
  exact ⟨mem_univ _, fun h => h rfl⟩

end
end ManuscriptAudit.SpecIntPointProductSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntPointProductSupport.closure_closedPrimes,
      ``ManuscriptAudit.SpecIntPointProductSupport.all_stalks_supported,
      ``ManuscriptAudit.SpecIntPointProductSupport.generic_germ_outside_input] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
