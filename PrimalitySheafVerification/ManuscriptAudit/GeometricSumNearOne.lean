import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-! One geometric-sum step near the identity has a unit quotient modulo the chosen integer. -/

namespace ManuscriptAudit.GeometricSumNearOne

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- When z≡1 mod m², the sum of its first m powers is m times an element congruent to 1 mod m. -/
theorem exists_unit_quotient (m : ℕ) (z : R) (h : (m : R) ^ 2 ∣ z - 1) :
    ∃ u : R, (∑ i ∈ Finset.range m, z ^ i) = (m : R) * (1 + (m : R) * u) := by
  have hEach (i : ℕ) : (m : R) ^ 2 ∣ z ^ i - 1 :=
    dvd_trans h (sub_one_dvd_pow_sub_one z i)
  have hSum : (m : R) ^ 2 ∣ ∑ i ∈ Finset.range m, (z ^ i - 1) :=
    Finset.dvd_sum (fun i _ => hEach i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_one] at hSum
  obtain ⟨u, hu⟩ := hSum
  refine ⟨u, ?_⟩
  calc
    _ = ((∑ i ∈ Finset.range m, z ^ i) - (m : R)) + (m : R) := by abel
    _ = _ := by rw [hu]; ring

end ManuscriptAudit.GeometricSumNearOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GeometricSumNearOne.exists_unit_quotient
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
