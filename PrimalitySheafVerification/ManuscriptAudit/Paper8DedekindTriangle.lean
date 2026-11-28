import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The weighted lattice triangle under the reciprocal rational slope, evaluated by rows and columns. -/

namespace ManuscriptAudit.Paper8DedekindTriangle

open Finset

private theorem sum_range_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
  have h := Finset.sum_range_id_mul_two (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have h' := congrArg (fun a : ℕ => (a : ℚ)) h
  push_cast at h'
  linarith

def floorSlope {k : ℕ} (h : ℕ) (j : Fin k) : ℕ := (h * j.val) / k

theorem floorSlope_lt {h k : ℕ} (hk : 0 < k) (j : Fin k) (hh : 0 < h) :
    floorSlope h j < h := by
  unfold floorSlope
  apply (Nat.div_lt_iff_lt_mul hk).2
  exact Nat.mul_lt_mul_of_pos_left j.isLt hh

private def triangleWeight {h k : ℕ} (j : Fin k) (v : Fin h) : ℚ :=
  if k * v.val ≤ h * j.val then (v.val : ℚ) else 0

private theorem row_sum {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (j : Fin k) :
    (∑ v : Fin h, triangleWeight j v) =
      (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1) / 2 := by
  let q := floorSlope h j
  let b : Fin h := ⟨q, floorSlope_lt hk j hh⟩
  have hCond (v : Fin h) : k * v.val ≤ h * j.val ↔ v.val ≤ q := by
    unfold q floorSlope
    rw [Nat.le_div_iff_mul_le hk, mul_comm v.val k]
  simp_rw [triangleWeight, hCond]
  rw [← Finset.sum_filter]
  have hF : (Finset.univ.filter (fun v : Fin h => v.val ≤ q)) = Iic b := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    rfl
  rw [hF]
  calc
    (∑ v ∈ Iic b, (v.val : ℚ)) =
        ∑ u ∈ (Iic b).map Fin.valEmbedding, (u : ℚ) := by simpa only [Finset.sum_map]
    _ = ∑ u ∈ range (q + 1), (u : ℚ) := by
      rw [Fin.map_valEmbedding_Iic]
      have hI : Iic (b.val) = range (q + 1) := by
        ext u
        simp only [Finset.mem_Iic, Finset.mem_range]
        change u ≤ q ↔ u < q + 1
        omega
      rw [hI]
    _ = _ := sum_range_rat q

private theorem column_sum {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) (v : Fin h) :
    (∑ j : Fin k, triangleWeight j v) =
      (v.val : ℚ) * ((k - 1 - floorSlope k v : ℕ) : ℚ) := by
  by_cases hv : v.val = 0
  · simp [triangleWeight, hv]
  let q := floorSlope k v
  let b : Fin k := ⟨q, floorSlope_lt hh v hk⟩
  have hCond (j : Fin k) : k * v.val ≤ h * j.val ↔ q < j.val := by
    have hn : k * v.val ≠ h * j.val := by
      intro he
      have hd : h ∣ k * v.val := ⟨j.val, he⟩
      have hD : h ∣ v.val := (hC.dvd_mul_left).1 hd
      exact (not_le_of_gt v.isLt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hv) hD)
    change k * v.val ≤ h * j.val ↔ k * v.val / h < j.val
    rw [Nat.div_lt_iff_lt_mul hh, mul_comm j.val h]
    exact ⟨fun h => lt_of_le_of_ne h hn, le_of_lt⟩
  simp_rw [triangleWeight, hCond]
  rw [← Finset.sum_filter]
  have hF : (Finset.univ.filter (fun j : Fin k => q < j.val)) = Ioi b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    rfl
  rw [hF, Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul]
  change (((k - 1 - q : ℕ) : ℚ)) * (v.val : ℚ) = (v.val : ℚ) * ((k - 1 - q : ℕ) : ℚ)
  exact mul_comm _ _

theorem floorSlope_quadratic_sum {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hC : h.Coprime k) :
    (∑ j : Fin k, (floorSlope h j : ℚ) * ((floorSlope h j : ℚ) + 1)) =
      2 * ∑ v : Fin h, (v.val : ℚ) * ((k - 1 - floorSlope k v : ℕ) : ℚ) := by
  calc
    _ = 2 * ∑ j : Fin k, ∑ v : Fin h, triangleWeight j v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [row_sum hh hk]
      ring
    _ = 2 * ∑ v : Fin h, ∑ j : Fin k, triangleWeight j v := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by simp_rw [column_sum hh hk hC]

end ManuscriptAudit.Paper8DedekindTriangle

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindTriangle.floorSlope_quadratic_sum
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
