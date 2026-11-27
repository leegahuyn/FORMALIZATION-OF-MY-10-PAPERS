import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat

/-! An eventually exact geometric sequence with decreasing factors is exact at every level. -/

namespace ManuscriptAudit.MonotoneCardinalFactors

/-- Successive integer factors cannot start larger and later recover an exact geometric sequence. -/
theorem exact_of_eventually_exact (a c : ℕ → ℕ) {d N : ℕ} (hd : 0 < d)
    (h0 : c 0 = 1) (hFactor : ∀ n, c (n + 1) = a n * c n)
    (hMono : Antitone a) (hTail : ∀ n, N ≤ n → c n = d ^ n) :
    (∀ n, a n = d) ∧ ∀ n, c n = d ^ n := by
  have ht (n : ℕ) (hn : N ≤ n) : a n = d := by
    have h := hFactor n
    rw [hTail (n + 1) (by omega), hTail n hn, pow_succ, mul_comm (d ^ n) d] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hd n) h.symm
  have ha (n : ℕ) : d ≤ a n := by
    have h := hMono (le_max_right N n)
    rwa [ht (max N n) (le_max_left N n)] at h
  have hc (n : ℕ) : d ^ n ≤ c n := by
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      rw [hFactor, pow_succ, mul_comm (d ^ n) d]
      exact Nat.mul_le_mul (ha n) ih
  have he (n : ℕ) : a n = d := by
    apply le_antisymm _ (ha n)
    by_contra! hLarge
    have hNext : d ^ (n + 1) < c (n + 1) := by
      rw [hFactor, pow_succ, mul_comm (d ^ n) d]
      exact (Nat.mul_lt_mul_of_pos_right hLarge (pow_pos hd n)).trans_le
        (Nat.mul_le_mul_left (a n) (hc n))
    have hLater (j : ℕ) : d ^ (n + 1 + j) < c (n + 1 + j) := by
      induction j with
      | zero => exact hNext
      | succ j ih =>
        rw [Nat.add_succ, hFactor, pow_succ, mul_comm (d ^ (n + 1 + j)) d]
        exact (Nat.mul_lt_mul_of_pos_left ih hd).trans_le
          (Nat.mul_le_mul_right (c (n + 1 + j)) (ha (n + 1 + j)))
    have h := hLater N
    rw [hTail _ (by omega : N ≤ n + 1 + N)] at h
    exact (lt_irrefl _) h
  refine ⟨he, fun n => ?_⟩
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [hFactor, he, ih, pow_succ, mul_comm]

end ManuscriptAudit.MonotoneCardinalFactors

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MonotoneCardinalFactors.exact_of_eventually_exact
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
