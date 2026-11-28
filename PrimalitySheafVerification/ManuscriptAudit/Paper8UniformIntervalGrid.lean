import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Explicit uniform partitions supply arbitrarily small positive meshes on a compact interval. -/

namespace ManuscriptAudit.Paper8UniformIntervalGrid

open Set

noncomputable section

def gridEndpoint (a b : ℝ) (n i : ℕ) : ℝ := a + ((b - a) / (n : ℝ)) * (i : ℝ)

theorem gridEndpoint_zero (a b : ℝ) (n : ℕ) : gridEndpoint a b n 0 = a := by
  simp [gridEndpoint]

theorem gridEndpoint_last (a b : ℝ) {n : ℕ} (hn : 0 < n) : gridEndpoint a b n n = b := by
  unfold gridEndpoint
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ h]
  ring

theorem gridEndpoint_strictMono {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (gridEndpoint a b n) := by
  intro i j hij
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hIJ : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  exact add_lt_add_left (mul_lt_mul_of_pos_left hIJ (div_pos (sub_pos.mpr hab) hN)) a

theorem gridEndpoint_step (a b : ℝ) (n i : ℕ) :
    gridEndpoint a b n (i + 1) - gridEndpoint a b n i = (b - a) / (n : ℝ) := by
  unfold gridEndpoint
  push_cast
  ring

theorem exists_grid_mesh_le {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, gridEndpoint a b n (i + 1) - gridEndpoint a b n i ≤ δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hR : (0 : ℝ) < n := (div_pos (sub_pos.mpr hab) hδ).trans hn
  have hN : 0 < n := by exact_mod_cast hR
  refine ⟨n, hN, fun i => ?_⟩
  rw [gridEndpoint_step]
  apply (div_le_iff₀ hR).mpr
  simpa only [mul_comm δ (n : ℝ)] using ((div_lt_iff₀ hδ).mp hn).le

theorem exists_mem_gridInterval {X : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : x ∈ Icc (X 0) (X n)) :
    ∃ i : Fin n, x ∈ Icc (X (i : ℕ)) (X ((i : ℕ) + 1)) := by
  have hPred : ∃ i : ℕ, x ≤ X (i + 1) := by
    refine ⟨n - 1, ?_⟩
    rw [show n - 1 + 1 = n by omega]
    exact hx.2
  let i := Nat.find hPred
  have hUp : x ≤ X (i + 1) := Nat.find_spec hPred
  have hN : i < n := by
    have hi : i ≤ n - 1 := by
      apply Nat.find_min' hPred
      rw [show n - 1 + 1 = n by omega]
      exact hx.2
    omega
  refine ⟨⟨i, hN⟩, ?_, hUp⟩
  by_cases h : i = 0
  · simpa only [h] using hx.1
  · have hlt : i - 1 < i := by omega
    have hNot := Nat.find_min hPred hlt
    have hEq : i - 1 + 1 = i := by omega
    exact le_of_lt (lt_of_not_ge (show ¬ x ≤ X i by rwa [hEq] at hNot))

theorem gridInterval_subset {X : ℕ → ℝ} (hX : Monotone X) {n : ℕ} (i : Fin n) :
    Icc (X (i : ℕ)) (X ((i : ℕ) + 1)) ⊆ Icc (X 0) (X n) :=
  fun _ hx => ⟨(hX (Nat.zero_le i)).trans hx.1, hx.2.trans (hX (Nat.succ_le_of_lt i.isLt))⟩

end
end ManuscriptAudit.Paper8UniformIntervalGrid

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8UniformIntervalGrid.exists_grid_mesh_le,
      ``ManuscriptAudit.Paper8UniformIntervalGrid.exists_mem_gridInterval] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
