import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.MonotoneCardinalFactors

/-! Cofinally exact cardinalities suffice for decreasing successive factors. -/

namespace ManuscriptAudit.MonotoneCofinalFactors

/-- Exact geometric growth at arbitrarily large indices forces every factor and cardinality. -/
theorem exact_of_cofinal_exact (a c : ℕ → ℕ) {d : ℕ} (hd : 0 < d)
    (h0 : c 0 = 1) (hFactor : ∀ n, c (n + 1) = a n * c n)
    (hMono : Antitone a) (hCofinal : ∀ n, ∃ m, n ≤ m ∧ c m = d ^ m) :
    (∀ n, a n = d) ∧ ∀ n, c n = d ^ n := by
  have hLower (n : ℕ) : d ≤ a n := by
    by_contra! hBelow
    obtain ⟨q, hq, heq⟩ := hCofinal n
    have hBound (m : ℕ) (hm : q ≤ m) : a m < d :=
      (hMono (hq.trans hm)).trans_lt hBelow
    have hStrict (j : ℕ) : c (q + 1 + j) < d ^ (q + 1 + j) := by
      induction j with
      | zero =>
          rw [Nat.add_zero, hFactor, heq, pow_succ, mul_comm (d ^ q)]
          exact Nat.mul_lt_mul_of_pos_right (hBound q le_rfl) (pow_pos hd q)
      | succ j ih =>
          rw [Nat.add_succ, hFactor, pow_succ, mul_comm (d ^ (q + 1 + j))]
          exact (Nat.mul_le_mul_right _ (hBound (q + 1 + j) (by omega)).le).trans_lt
            (Nat.mul_lt_mul_of_pos_left ih hd)
    obtain ⟨m, hm, hem⟩ := hCofinal (q + 1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact (ne_of_lt (hStrict j)) hem
  have hCardLower (n : ℕ) : d ^ n ≤ c n := by
    induction n with
    | zero => simp [h0]
    | succ n ih =>
        rw [hFactor, pow_succ, mul_comm (d ^ n)]
        exact Nat.mul_le_mul (hLower n) ih
  have hExact (n : ℕ) : a n = d := by
    apply le_antisymm _ (hLower n)
    by_contra! hAbove
    have hStrict (j : ℕ) : d ^ (n + 1 + j) < c (n + 1 + j) := by
      induction j with
      | zero =>
          rw [Nat.add_zero, hFactor, pow_succ, mul_comm (d ^ n)]
          exact (Nat.mul_lt_mul_of_pos_right hAbove (pow_pos hd n)).trans_le
            (Nat.mul_le_mul_left _ (hCardLower n))
      | succ j ih =>
          rw [Nat.add_succ, hFactor, pow_succ, mul_comm (d ^ (n + 1 + j))]
          exact (Nat.mul_lt_mul_of_pos_left ih hd).trans_le
            (Nat.mul_le_mul_right _ (hLower (n + 1 + j)))
    obtain ⟨m, hm, hem⟩ := hCofinal (n + 1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact (ne_of_gt (hStrict j)) hem
  refine ⟨hExact, fun n => ?_⟩
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [hFactor, hExact, ih, pow_succ, mul_comm]

end ManuscriptAudit.MonotoneCofinalFactors

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MonotoneCofinalFactors.exact_of_cofinal_exact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
