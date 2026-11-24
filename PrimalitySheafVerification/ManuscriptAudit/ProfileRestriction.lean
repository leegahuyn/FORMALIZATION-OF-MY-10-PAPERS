import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The direction of restriction for coprime parameter sets

Paper 1, p. 6, lets a profile over D(f) have support coprime to f.
The paper asks that refinement restriction keep the profile unchanged.
D(2) is a nonempty refinement of D(1), but the support 2 then ceases
to be allowed.
-/

namespace ManuscriptAudit.ProfileRestriction

theorem paper1_prime_two_open_refines_one :
    PrimeSpectrum.basicOpen (2 : ℤ) ≠ ⊥ ∧
      PrimeSpectrum.basicOpen (2 : ℤ) ≤ PrimeSpectrum.basicOpen 1 := by
  refine ⟨?_, ?_⟩
  · let x : PrimeSpectrum ℤ := ⟨⊥, inferInstance⟩
    have hx : x ∈ PrimeSpectrum.basicOpen (2 : ℤ) := by
      rw [PrimeSpectrum.mem_basicOpen]
      change (2 : ℤ) ∉ (⊥ : Ideal ℤ)
      simp
    intro h
    rw [h] at hx
    change False at hx
    exact hx
  · simp

/-- Any available profile of support two contradicts the printed
identity-on-parameters restriction along D(2) ⊆ D(1). -/
theorem paper1_profile_identity_restriction_impossible {P : Type*}
    (support : P → ℕ) (π : P) (hπ : support π = 2) :
    ¬ ∃ r : {x : P // Nat.Coprime (support x) 1} →
            {x : P // Nat.Coprime (support x) 2},
        ∀ x, (r x).val = x.val := by
  rintro ⟨r, hr⟩
  let x : {y : P // Nat.Coprime (support y) 1} := ⟨π, Nat.coprime_one_right _⟩
  have h := (r x).property
  rw [hr x] at h
  change Nat.Coprime (support π) 2 at h
  rw [hπ] at h
  exact (by decide : ¬ Nat.Coprime 2 2) h

end ManuscriptAudit.ProfileRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ProfileRestriction.paper1_prime_two_open_refines_one,
      ``ManuscriptAudit.ProfileRestriction.paper1_profile_identity_restriction_impossible] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
