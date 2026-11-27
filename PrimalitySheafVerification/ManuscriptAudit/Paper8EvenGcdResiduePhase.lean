import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdResiduePhase

/-!
# Even-gcd phases for the reciprocal residue rows

For gcd g=2h and reduced denominator D, the printed modulus is hD.
The reciprocal residue row reduces to the unshifted Dedekind
frequency with the signs proved below.
-/

namespace ManuscriptAudit.Paper8EvenGcdResiduePhase

open Paper8OddGcdResiduePhase (modulusSign residuePhase exp_negative_half_period)

noncomputable section

private theorem phase_at_even_modulus {k : ℕ} (hk : Even k) (h u : ℕ) :
    residuePhase k ((2 * h) * u) = (-1 : ℂ) ^ (h * u) := by
  have hSc : -(((2 * h) * u : ℕ) : ℝ) / 8 * (1 + 1 : ℝ) =
      -((h * u : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [residuePhase, hk.neg_one_pow, hSc, exp_negative_half_period]

theorem phase_of_odd_denominator (h D u : ℕ) (hD : Odd D) :
    residuePhase (h * D) ((2 * h) * u) = 1 := by
  rcases Nat.even_or_odd h with hH | hH
  · have hk : Even (h * D) := by
      obtain ⟨a, ha⟩ := hH
      refine ⟨a * D, ?_⟩
      rw [ha]
      ring
    have hu : Even (h * u) := by
      obtain ⟨a, ha⟩ := hH
      refine ⟨a * u, ?_⟩
      rw [ha]
      ring
    rw [phase_at_even_modulus hk, hu.neg_one_pow]
  · simp [residuePhase, (hH.mul hD).neg_one_pow]

theorem phase_of_even_denominator (h D u : ℕ) (hD : Even D) (hu : Odd u) :
    residuePhase (h * D) ((2 * h) * u) = (-1 : ℂ) ^ h := by
  have hk : Even (h * D) := by
    obtain ⟨a, ha⟩ := hD
    refine ⟨h * a, ?_⟩
    rw [ha]
    ring
  rw [phase_at_even_modulus hk, Nat.mul_comm h u, pow_mul, hu.neg_one_pow]

theorem combined_sign_modulus_zero_mod_four (h a u : ℕ) (hu : Odd u) :
    modulusSign (h * (4 * a)) * residuePhase (h * (4 * a)) ((2 * h) * u) = (-1 : ℂ) ^ h := by
  have hD : Even (4 * a) := ⟨2 * a, by ring⟩
  have hM : h * (4 * a) + 1 = 2 * (2 * h * a) + 1 := by ring
  have hDiv : (h * (4 * a) + 1) / 2 = 2 * h * a := by omega
  have hEven : Even (2 * h * a) := ⟨h * a, by ring⟩
  rw [modulusSign, hDiv, hEven.neg_one_pow, phase_of_even_denominator h _ u hD hu, one_mul]

theorem combined_sign_modulus_two_mod_four (h a u : ℕ) (hu : Odd u) :
    modulusSign (h * (4 * a + 2)) * residuePhase (h * (4 * a + 2)) ((2 * h) * u) = 1 := by
  have hD : Even (4 * a + 2) := ⟨2 * a + 1, by ring⟩
  have hM : h * (4 * a + 2) + 1 = 2 * (2 * h * a + h) + 1 := by ring
  have hDiv : (h * (4 * a + 2) + 1) / 2 = 2 * h * a + h := by omega
  have hEven : Even (2 * h * a) := ⟨h * a, by ring⟩
  have hSum : Even (h + h) := ⟨h, rfl⟩
  rw [modulusSign, hDiv, pow_add, hEven.neg_one_pow, one_mul,
    phase_of_even_denominator h _ u hD hu, ← pow_add, hSum.neg_one_pow]

end
end ManuscriptAudit.Paper8EvenGcdResiduePhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenGcdResiduePhase.phase_of_odd_denominator,
      ``ManuscriptAudit.Paper8EvenGcdResiduePhase.phase_of_even_denominator,
      ``ManuscriptAudit.Paper8EvenGcdResiduePhase.combined_sign_modulus_zero_mod_four,
      ``ManuscriptAudit.Paper8EvenGcdResiduePhase.combined_sign_modulus_two_mod_four] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
