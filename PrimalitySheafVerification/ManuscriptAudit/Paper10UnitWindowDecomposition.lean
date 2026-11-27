import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import PrimalitySheafVerification.ManuscriptAudit.Paper10SpectralTailEstimate

/-! The actual tail sum can be grouped into consecutive half-open unit windows. -/

namespace ManuscriptAudit.Paper10UnitWindowDecomposition

open Paper10SpectralTailEstimate

noncomputable section

variable {ι : Type*} (t : ι → ℝ) (R : ℝ) (S : ℕ → Finset ι)
variable (hS : ∀ (k : ℕ) (j : ι), j ∈ S k ↔ R + (k : ℝ) ≤ t j ∧ t j < R + (k : ℝ) + 1)

private abbrev Tail := {j : ι // R ≤ t j}

private def window (k : ℕ) : Set (Tail t R) := {j | j.val ∈ S k}

private theorem tail_in_unique_window (j : Tail t R) :
    ∃! k : ℕ, j ∈ window t R S k := by
  have hz : 0 ≤ t j.val - R := sub_nonneg.mpr j.property
  refine ⟨⌊t j.val-R⌋₊, ?_, ?_⟩
  · rw [window, Set.mem_setOf_eq, hS]
    exact ⟨by linarith only [Nat.floor_le hz], by linarith only [Nat.lt_floor_add_one (t j.val-R)]⟩
  · intro k hk
    have h := (hS k j.val).mp hk
    exact ((Nat.floor_eq_iff hz).mpr ⟨by linarith only [h.1], by linarith only [h.2]⟩).symm

private def windowIndices (k : ℕ) : window t R S k ≃ {j : ι // j ∈ S k} where
  toFun j := ⟨j.val.val, j.property⟩
  invFun j := ⟨⟨j.val, (le_add_of_nonneg_right (Nat.cast_nonneg k)).trans
    ((hS k j.val).mp j.property).1⟩, j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_tail_summable_and_bound (w : ι → ℝ)
    {C B : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) (A : ℕ)
    (hDecay : ∀ j : ι, R ≤ t j → |w j| ≤ B / (1+t j)^(A+3))
    (hCount : ∀ k : ℕ, ((S k).card : ℝ) ≤ C * (1 + R + (k : ℝ))) :
    Summable (fun j : {j : ι // R ≤ t j} => |w j.val|) ∧
      (∑' j : {j : ι // R ≤ t j}, |w j.val|) ≤
        (C*B / R^A) * (∑' k : ℕ, 1 / ((k : ℝ)+1)^2) := by
  let f (j : Tail t R) := |w j.val|
  let e := Set.sigmaEquiv (window t R S) (tail_in_unique_window t R S hS)
  let g (j : Σ k, window t R S k) := f j.2.val
  have hl (k : ℕ) (j : ι) (hj : j ∈ S k) := ((hS k j).mp hj).1
  have hD (k : ℕ) (j : ι) (hj : j ∈ S k) : |w j| ≤ B / (1+t j)^(A+3) :=
    hDecay j ((le_add_of_nonneg_right (Nat.cast_nonneg k)).trans (hl k j hj))
  obtain ⟨hShell, hBound⟩ := grouped_tail_summable_and_bound S t w hR hC hB A hl hD hCount
  have hFinite (k : ℕ) : Summable (fun j : window t R S k => f j.val) := by
    letI := Fintype.ofEquiv {j : ι // j ∈ S k} (windowIndices t R S hS k).symm
    exact summable_fintype _
  have hEq (k : ℕ) : (∑' j : window t R S k, f j.val) = ∑ j ∈ S k, |w j| := by
    calc
      _ = ∑' j : {j : ι // j ∈ S k}, |w j.val| := by
        exact (windowIndices t R S hS k).tsum_eq (fun j : {j : ι // j ∈ S k} => |w j.val|)
      _ = _ := Finset.tsum_subtype (S k) (fun j => |w j|)
  have hG : Summable g := by
    apply (summable_sigma_of_nonneg (fun _ => abs_nonneg _)).mpr
    refine ⟨hFinite, ?_⟩
    simp_rw [show ∀ k : ℕ, (∑' j : window t R S k, g ⟨k,j⟩) =
        ∑ j ∈ S k, |w j| from hEq]
    exact hShell
  have hF : Summable f := (e.summable_iff).mp hG
  refine ⟨hF, ?_⟩
  change (∑' j, f j) ≤ _
  calc
    (∑' j, f j) = ∑' j, g j := (e.tsum_eq f).symm
    _ = ∑' k, ∑ j ∈ S k, |w j| := hG.tsum_sigma.trans (tsum_congr hEq)
    _ ≤ _ := hBound

/-- The cutoff used in the manuscript gives the claimed uniform polynomial rate
when the decay and window bounds have the stated uniform constants. -/
theorem logarithmic_cutoff_bound (w : ι → ℝ) (T : ℝ) (hT : 1 ≤ T) (A : ℕ)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hWindows : ∀ (k : ℕ) (j : ι), j ∈ S k ↔
      T + (Real.log T)^2 + (k : ℝ) ≤ t j ∧ t j < T + (Real.log T)^2 + (k : ℝ) + 1)
    (hDecay : ∀ j : ι, T + (Real.log T)^2 ≤ t j → |w j| ≤ B / (1+t j)^(A+3))
    (hCount : ∀ k : ℕ, ((S k).card : ℝ) ≤ C * (1 + (T + (Real.log T)^2) + (k : ℝ))) :
    Summable (fun j : {j : ι // T + (Real.log T)^2 ≤ t j} => |w j.val|) ∧
      (∑' j : {j : ι // T + (Real.log T)^2 ≤ t j}, |w j.val|) ≤
        (C*B / T^A) * (∑' k : ℕ, 1 / ((k : ℝ)+1)^2) := by
  have hTR : T ≤ T + (Real.log T)^2 := le_add_of_nonneg_right (sq_nonneg _)
  have hR : 1 ≤ T + (Real.log T)^2 := hT.trans hTR
  obtain ⟨hs, hb⟩ := actual_tail_summable_and_bound t _ S hWindows w hR hC hB A hDecay hCount
  refine ⟨hs, hb.trans ?_⟩
  have hTA : T^A ≤ (T + (Real.log T)^2)^A := by gcongr <;> linarith
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_left (mul_nonneg hC hB)
      (pow_pos (by linarith : 0 < T) _) hTA
  · exact tsum_nonneg (fun _ => by positivity)

end
end ManuscriptAudit.Paper10UnitWindowDecomposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10UnitWindowDecomposition.actual_tail_summable_and_bound,
      ``ManuscriptAudit.Paper10UnitWindowDecomposition.logarithmic_cutoff_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
