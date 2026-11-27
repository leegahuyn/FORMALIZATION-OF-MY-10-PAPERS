import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper1NativeVisibilityGate

/-! Exact bounded completeness and the first missed-square failure of the native unit test. -/

namespace ManuscriptAudit.Paper1BoundedVisibility

open IntPrimeResidueFiber Paper1NativeVisibilityGate

theorem correctness_through_iff (U : Set (PrimeSpectrum ℤ)) (B : ℕ) :
    (∀ X : ℕ, 2 ≤ X → X ≤ B → (passes U X ↔ X.Prime)) ↔
      (∀ (p : ℕ) [Fact p.Prime], p ≤ B.sqrt → closedPoint p ∈ U) := by
  constructor
  · intro h p hp hSmall
    by_contra hMiss
    obtain ⟨hPass, hNot⟩ := omitted_prime_square_passes p hMiss
    have hTwo : 2 ≤ p^2 := by nlinarith [hp.out.two_le]
    have hBound : p^2 ≤ B := by simpa only [pow_two] using Nat.le_sqrt.mp hSmall
    exact hNot ((h (p^2) hTwo hBound).1 hPass)
  · intro h X hX hBound
    refine ⟨?_, prime_passes⟩
    intro hPass
    have hFull : ∀ (p : ℕ) [Fact p.Prime],
        closedPoint p ∈ (Set.univ : Set (PrimeSpectrum ℤ)) := fun _ _ => Set.mem_univ _
    apply (((global_correctness_iff_full_visibility Set.univ).2 hFull) X hX).1
    intro p hp _ hpX
    have hpB : p ≤ B.sqrt := Nat.le_sqrt.mpr ((Nat.le_sqrt.mp hpX).trans hBound)
    exact hPass p (h p hpB) hpX

theorem principal_correctness_through_iff (f : ℤ) (B : ℕ) :
    (∀ X : ℕ, 2 ≤ X → X ≤ B →
        (passes (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)) X ↔ X.Prime)) ↔
      (∀ (p : ℕ) [Fact p.Prime], p ≤ B.sqrt → ¬ (p : ℤ) ∣ f) := by
  rw [correctness_through_iff]
  constructor
  · intro h p hp hpB
    have hVisible := h p hpB
    change f ∉ (closedPoint p).asIdeal at hVisible
    simpa only [closedPoint_ideal p, Ideal.mem_span_singleton] using hVisible
  · intro h p hp hpB
    change f ∉ (closedPoint p).asIdeal
    simpa only [closedPoint_ideal p, Ideal.mem_span_singleton] using h p hpB

theorem first_false_positive_of_least_omitted (U : Set (PrimeSpectrum ℤ))
    (p : ℕ) [Fact p.Prime] (hMiss : closedPoint p ∉ U)
    (hLower : ∀ (q : ℕ) [Fact q.Prime], q < p → closedPoint q ∈ U) :
    (passes U (p^2) ∧ ¬ (p^2).Prime) ∧
      ∀ X : ℕ, 2 ≤ X → X < p^2 → (passes U X ↔ X.Prime) := by
  refine ⟨omitted_prime_square_passes p hMiss, ?_⟩
  intro X hX hBefore
  apply ((correctness_through_iff U X).2 ?_) X hX le_rfl
  intro q hq hSmall
  apply hLower q
  by_contra! h
  have hle : p * p ≤ q * q := Nat.mul_le_mul h h
  have hX' : q * q ≤ X := Nat.le_sqrt.mp hSmall
  rw [pow_two] at hBefore
  exact (not_le_of_gt hBefore) (hle.trans hX')

end ManuscriptAudit.Paper1BoundedVisibility

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1BoundedVisibility.correctness_through_iff,
      ``ManuscriptAudit.Paper1BoundedVisibility.principal_correctness_through_iff,
      ``ManuscriptAudit.Paper1BoundedVisibility.first_false_positive_of_least_omitted] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
