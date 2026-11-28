import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindResidueMoments

/-! Native parity of the weighted floor moment that supplies the quadratic character at prime moduli. -/

namespace ManuscriptAudit.Paper8DedekindFloorParity

open Finset Paper8DedekindResidueMoments

noncomputable section

private theorem floor_complement {h k j : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hj0 : 0 < j) (hjk : j < k) (hr : (h * j) % k ≠ 0) :
    (h * (k - j)) / k = h - ((h * j) / k + 1) := by
  have hJ : 0 < h * j := Nat.mul_pos hh hj0
  have hL : h * j - 1 < k * h := by
    have h := Nat.mul_lt_mul_of_pos_left hjk hh
    rw [Nat.mul_comm h k] at h
    omega
  have hRep : (h * j) % k + k * ((h * j) / k) = h * j := Nat.mod_add_div _ _
  have hPred : h * j - 1 = ((h * j) % k - 1) + k * ((h * j) / k) := by omega
  have hPrior : (h * j - 1) / k = (h * j) / k := by
    have hR : (h * j) % k - 1 < k := by
      have h := Nat.mod_lt (h * j) hk
      omega
    conv_lhs => rw [hPred, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hR, zero_add]
  have hMul : h * (k - j) = k * h - (h * j - 1 + 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm h k, Nat.sub_add_cancel hJ]
  rw [hMul, Nat.mul_sub_div _ _ _ hL, hPrior]

def dedekindFloorWeight (h k : ℕ) : ℕ := ∑ j : Fin k, j.val * ((h * j.val) / k)

def halfFloorWeight (h k : ℕ) : ℕ := ∑ j ∈ range (k / 2), (h * (j + 1)) / k

theorem dedekindFloorWeight_parity {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hC : h.Coprime k) : dedekindFloorWeight h k % 2 = halfFloorWeight h k % 2 := by
  have hk0 : 0 < k := by omega
  have hh0 : 0 < h := by omega
  let f (j : ℕ) : ZMod 2 := (j : ZMod 2) * (((h * j) / k : ℕ) : ZMod 2)
  let m := k / 2
  have hK : k = m + m + 1 := by dsimp only [m]; omega
  have h0 : f 0 = 0 := by simp [f]
  have hKcast : (k : ZMod 2) = 1 := by
    change (k : ZMod 2) = ((1 : ℕ) : ZMod 2)
    exact (ZMod.natCast_eq_natCast_iff' k 1 2).2 (by simpa using hk)
  have hPair (j : ℕ) (hj0 : 0 < j) (hjk : j < k) :
      f j + f (k - j) = (((h * j) / k : ℕ) : ZMod 2) := by
    let i : Fin k := ⟨j, hjk⟩
    let z : Fin k := ⟨0, hk0⟩
    have hR : (h * j) % k ≠ 0 := by
      intro h
      have he : residuePerm h k hk0 hC i = residuePerm h k hk0 hC z := by
        apply Fin.ext
        simp [residuePerm_val, i, z, h]
      have hj := congrArg Fin.val ((residuePerm h k hk0 hC).injective he)
      exact hj0.ne' hj
    have hDiv := floor_complement hh0 hk0 hj0 hjk hR
    have hQ : (h * j) / k < h := (Nat.div_lt_iff_lt_mul hk0).2 (Nat.mul_lt_mul_of_pos_left hjk hh0)
    have hQpar : ((h * (k - j)) / k) % 2 = ((h * j) / k) % 2 := by
      rw [hDiv]
      omega
    have hCast : ((((h * (k - j)) / k : ℕ) : ZMod 2)) = (((h * j) / k : ℕ) : ZMod 2) :=
      (ZMod.natCast_eq_natCast_iff' _ _ 2).2 hQpar
    unfold f
    rw [hCast, ← add_mul, ← Nat.cast_add, show j + (k - j) = k by omega, hKcast, one_mul]
  have hSplit : (∑ j ∈ range k, f j) =
      (∑ j ∈ range m, f (j + 1)) + ∑ j ∈ range m, f (m + j + 1) := by
    rw [hK, Finset.sum_range_succ', h0]
    simp only [zero_add, add_zero, Finset.sum_range_add, Nat.add_comm m]
  have hReflect : (∑ j ∈ range m, f (m + j + 1)) = ∑ j ∈ range m, f (k - (j + 1)) := by
    calc
      _ = ∑ j ∈ range m, f (m + (m - 1 - j) + 1) :=
        (Finset.sum_range_reflect (fun t => f (m + t + 1)) m).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hJ := Finset.mem_range.mp hj
        congr 1
        omega
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).1
  unfold dedekindFloorWeight halfFloorWeight
  push_cast
  rw [Fin.sum_univ_eq_sum_range]
  change (∑ j ∈ range k, f j) = ∑ j ∈ range m, (((h * (j + 1)) / k : ℕ) : ZMod 2)
  rw [hSplit, hReflect, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hJ := Finset.mem_range.mp hj
  exact hPair (j + 1) (by omega) (by omega)

theorem legendreSym_eq_weighted_floor {p h : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hh : h % 2 = 1) (hC : h.Coprime p) :
    legendreSym p (h : ℤ) = (-1 : ℤ) ^ dedekindFloorWeight h p := by
  have hp2 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp
  have hZ : (h : ZMod p) ≠ 0 := by
    have hu := (ZMod.unitOfCoprime h hC).ne_zero
    exact hu
  have hE := ZMod.eisenstein_lemma hp hh hZ
  have hSum : (∑ j ∈ Ico 1 (p / 2).succ, j * h / p) = halfFloorWeight h p := by
    rw [Finset.sum_Ico_eq_sum_range]
    unfold halfFloorWeight
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.mul_comm]
  rw [hSum] at hE
  calc
    _ = (-1 : ℤ) ^ halfFloorWeight h p := hE
    _ = (-1 : ℤ) ^ (halfFloorWeight h p % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℤ) ^ (dedekindFloorWeight h p % 2) := by rw [dedekindFloorWeight_parity hh hp2 hC]
    _ = _ := (neg_one_pow_eq_pow_mod_two _).symm

end
end ManuscriptAudit.Paper8DedekindFloorParity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindFloorParity.legendreSym_eq_weighted_floor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
