import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

namespace ManuscriptAudit.Paper07

private noncomputable def canonicalPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

private noncomputable def canonicalModulus (n : ℕ) : ℕ :=
  canonicalPrime n + (4 - 1)

private noncomputable def canonicalPeriod (n k : ℕ) : ℕ :=
  Nat.lcm (canonicalModulus n) (canonicalPrime n ^ k)

inductive Gate where
  | numeric | modular | pAdic | elliptic

/-- Paper 7, p. 231 (EC) and p. 245, Theorem .1. The elliptic gate on the
fixed working open asks that every visible prime lie on the discriminant
open, written here as `U ≤ D(Δ)`. The paper takes the smooth-fiber and
Hensel conditions to hold on this locus. The profile fixes `U` and `Δ` for
all candidates `X`. The numeric and p-adic gates may be arbitrary predicates
on `X`. -/
private noncomputable def gatePass {n : ℕ} (numeric pAdic : ℕ → Prop)
    (Δ : ℤ) (U : TopologicalSpace.Opens (PrimeSpectrum ℤ))
    (W : Set (ZMod (canonicalModulus n))) (X : ℕ) : Gate → Prop
  | .numeric => numeric X
  | .modular => (X : ZMod (canonicalModulus n)) ∈ W
  | .pAdic => pAdic X
  | .elliptic => U ≤ PrimeSpectrum.basicOpen Δ

private noncomputable def fixedProfileIndependent (n k : ℕ) (numeric pAdic : ℕ → Prop)
    (Δ : ℤ) (U : TopologicalSpace.Opens (PrimeSpectrum ℤ))
    (W : Set (ZMod (canonicalModulus n))) : Prop :=
  ∀ failing : Gate, ∃ X₀ : ℕ, ∀ X : ℕ, X ≡ X₀ [MOD canonicalPeriod n k] →
    (∀ other : Gate, other ≠ failing → gatePass numeric pAdic Δ U W X other) ∧
      ¬ gatePass numeric pAdic Δ U W X failing

/-- Every residue passes the modular gate when the admissible set is the
whole quotient. The origin of the claimed modular-failure progression then
gives a contradiction. -/
theorem page245_no_modular_failure_for_all_residues (n k : ℕ)
    (numeric pAdic : ℕ → Prop) (Δ : ℤ)
    (U : TopologicalSpace.Opens (PrimeSpectrum ℤ)) :
    ¬ fixedProfileIndependent n k numeric pAdic Δ U Set.univ := by
  intro hindependent
  obtain ⟨X₀, hprogression⟩ := hindependent .modular
  exact (hprogression X₀ (Nat.ModEq.refl X₀)).2 (Set.mem_univ _)

/-- Every candidate passes the discriminant gate on the stipulated good
working open. The full independence assertion thus fails for any allowed
residue set, including proper subsets. -/
theorem page245_no_elliptic_failure_inside_good_open (n k : ℕ)
    (numeric pAdic : ℕ → Prop) (Δ : ℤ)
    (U : TopologicalSpace.Opens (PrimeSpectrum ℤ))
    (W : Set (ZMod (canonicalModulus n)))
    (hgood : U ≤ PrimeSpectrum.basicOpen Δ) :
    ¬ fixedProfileIndependent n k numeric pAdic Δ U W := by
  intro hindependent
  obtain ⟨X₀, hprogression⟩ := hindependent .elliptic
  exact (hprogression X₀ (Nat.ModEq.refl X₀)).2 hgood

/-- Theorem .1 at the first admitted index and precision, with the whole
discriminant open and all residues allowed. -/
theorem page245_quantified_independence_false
    (numeric pAdic : ℕ → ℕ → ℕ → Prop) (Δ : ℤ) :
    ¬ (∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, 1 ≤ k →
      ∀ U : TopologicalSpace.Opens (PrimeSpectrum ℤ), U ≤ PrimeSpectrum.basicOpen Δ →
      ∀ W : Set (ZMod (canonicalModulus n)), W.Nonempty →
        fixedProfileIndependent n k (numeric n k) (pAdic n k) Δ U W) := by
  intro hindependent
  have hW : (Set.univ : Set (ZMod (canonicalModulus 3))).Nonempty :=
    ⟨0, Set.mem_univ _⟩
  exact page245_no_modular_failure_for_all_residues 3 1 (numeric 3 1) (pAdic 3 1) Δ
    (PrimeSpectrum.basicOpen Δ)
    (hindependent 3 (by decide) 1 (by decide) (PrimeSpectrum.basicOpen Δ) le_rfl Set.univ hW)

/-- The counterexample specializes to the third prime, modulus eight and
progression period forty. -/
theorem page245_third_prime_profile :
    canonicalPrime 3 = 5 ∧ canonicalModulus 3 = 8 ∧ canonicalPeriod 3 1 = 40 := by
  have hprime : canonicalPrime 3 = 5 := Nat.nth_prime_two_eq_five
  refine ⟨hprime, ?_, ?_⟩
  · simp [canonicalModulus, hprime]
  · simpa [canonicalPeriod, canonicalModulus, hprime] using
      (show Nat.lcm 8 5 = 40 by decide)

end ManuscriptAudit.Paper07

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Paper07.page245_no_modular_failure_for_all_residues,
    ``ManuscriptAudit.Paper07.page245_no_elliptic_failure_inside_good_open,
    ``ManuscriptAudit.Paper07.page245_quantified_independence_false,
    ``ManuscriptAudit.Paper07.page245_third_prime_profile] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
