import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper1NativeVisibilityGate

/-! The square-root unit gate is complete across a genuine cover of Spec ℤ. -/

namespace ManuscriptAudit.Paper1PrincipalGateCompleteness

open IntPrimeResidueFiber Paper1NativeVisibilityGate

theorem passes_union_iff {ι : Type*} (U : ι → Set (PrimeSpectrum ℤ)) (X : ℕ) :
    passes (⋃ i, U i) X ↔ ∀ i, passes (U i) X := by
  constructor
  · intro h i p hp hvisible hsmall
    exact h p (Set.mem_iUnion.mpr ⟨i, hvisible⟩) hsmall
  · intro h p hp hvisible hsmall
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hvisible
    exact h i p hi hsmall

theorem principal_cover_unit_gate_iff_prime {ι : Type*} (f : ι → ℤ)
    (hcover : (⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum ℤ))) = Set.univ)
    {X : ℕ} (hX : 2 ≤ X) :
    (∀ i, passes (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum ℤ)) X) ↔ X.Prime := by
  rw [← passes_union_iff (fun i => (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum ℤ))), hcover]
  have hfull : ∀ (p : ℕ) [Fact p.Prime], closedPoint p ∈ (Set.univ : Set (PrimeSpectrum ℤ)) :=
    fun _ _ => Set.mem_univ _
  exact ((global_correctness_iff_full_visibility (Set.univ : Set (PrimeSpectrum ℤ))).mpr hfull) X hX

theorem principal_open_is_complete_iff_unit (f : ℤ) :
    (∀ X : ℕ, 2 ≤ X → (passes (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)) X ↔ X.Prime)) ↔
      IsUnit f := by
  rw [global_correctness_iff_full_visibility]
  constructor
  · intro h
    by_contra hn
    have hne : f.natAbs ≠ 1 := by
      intro he
      rcases Int.natAbs_eq f with hf | hf
      · have h1 : f = 1 := by omega
        rw [h1] at hn
        exact hn isUnit_one
      · have h1 : f = -1 := by omega
        rw [h1] at hn
        exact hn ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
    letI : Fact p.Prime := ⟨hp⟩
    have he := h p
    change f ∉ (closedPoint p).asIdeal at he
    apply he
    rw [closedPoint_ideal p, Ideal.mem_span_singleton, Int.natCast_dvd]
    exact hd
  · intro hu p hp
    change f ∉ (closedPoint p).asIdeal
    intro h
    exact (closedPoint p : PrimeSpectrum ℤ).isPrime.ne_top
      ((closedPoint p).asIdeal.eq_top_of_isUnit_mem h hu)

end ManuscriptAudit.Paper1PrincipalGateCompleteness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1PrincipalGateCompleteness.passes_union_iff,
      ``ManuscriptAudit.Paper1PrincipalGateCompleteness.principal_cover_unit_gate_iff_prime,
      ``ManuscriptAudit.Paper1PrincipalGateCompleteness.principal_open_is_complete_iff_unit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
