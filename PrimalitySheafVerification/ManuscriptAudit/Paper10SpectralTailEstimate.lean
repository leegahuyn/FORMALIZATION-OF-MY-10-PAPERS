import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith

/-! Uniform power decay and linear window density give a uniform bound for grouped spectral tails. -/

namespace ManuscriptAudit.Paper10SpectralTailEstimate

noncomputable section

private lemma shell_estimate {ι : Type*} (s : Finset ι) (t w : ι → ℝ)
    {R C B : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) (A k : ℕ)
    (ht : ∀ j ∈ s, R + (k : ℝ) ≤ t j)
    (hw : ∀ j ∈ s, |w j| ≤ B / (1 + t j)^(A+3))
    (hcount : (s.card : ℝ) ≤ C * (1 + R + (k : ℝ))) :
    (∑ j ∈ s, |w j|) ≤ (C*B / R^A) * (1 / ((k : ℝ)+1)^2) := by
  let d := 1 + R + (k : ℝ)
  have hR0 : 0 < R := by linarith
  have hd : 0 < d := by dsimp only [d]; positivity
  have hk0 : 0 < (k : ℝ)+1 := by positivity
  have hnum : 0 ≤ C*B := mul_nonneg hC hB
  have hRle : R ≤ d := by dsimp only [d]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hkle : (k : ℝ)+1 ≤ d := by dsimp only [d]; linarith
  have hRD : R^A ≤ d^A := by gcongr
  have hkD : ((k : ℝ)+1)^2 ≤ d^2 := by gcongr
  have hprod : R^A * ((k : ℝ)+1)^2 ≤ d^(A+2) := by
    rw [pow_add]
    exact mul_le_mul hRD hkD (by positivity) (by positivity)
  have hterm (j : ι) (hj : j ∈ s) : |w j| ≤ B / d^(A+3) := by
    have hdt : d ≤ 1+t j := by dsimp only [d]; linarith only [ht j hj]
    have hc : d^(A+3) ≤ (1+t j)^(A+3) := by gcongr
    apply (hw j hj).trans
    exact div_le_div_of_nonneg_left hB (by positivity) hc
  calc
    (∑ j ∈ s, |w j|) ≤ ∑ _j ∈ s, B / d^(A+3) := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (B / d^(A+3)) := by simp
    _ ≤ (C*d) * (B / d^(A+3)) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = C*B / d^(A+2) := by
      rw [show d^(A+3) = d^(A+2) * d from pow_succ d (A+2)]
      field_simp [hd.ne', pow_ne_zero _ hd.ne'] <;> ring
    _ ≤ (C*B) / (R^A * ((k : ℝ)+1)^2) :=
      div_le_div_of_nonneg_left hnum (by positivity) hprod
    _ = (C*B / R^A) * (1 / ((k : ℝ)+1)^2) := by rw [mul_one_div, div_div]

/-- The shell sets and bound may depend on the parameter. The constants C and B in the
hypotheses control the sum uniformly after factoring out the indicated power of the cutoff. -/
theorem grouped_tail_summable_and_bound {ι : Type*} (S : ℕ → Finset ι) (t w : ι → ℝ)
    {R C B : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) (A : ℕ)
    (ht : ∀ k j, j ∈ S k → R + (k : ℝ) ≤ t j)
    (hw : ∀ k j, j ∈ S k → |w j| ≤ B / (1+t j)^(A+3))
    (hcount : ∀ k : ℕ, ((S k).card : ℝ) ≤ C * (1 + R + (k : ℝ))) :
    Summable (fun k => ∑ j ∈ S k, |w j|) ∧
      (∑' k, ∑ j ∈ S k, |w j|) ≤ (C*B / R^A) * (∑' k : ℕ, 1 / ((k : ℝ)+1)^2) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ)+1)^2) := by
    have h := Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mp h
  have hmajor := hbase.mul_left (C*B / R^A)
  have hterm (k : ℕ) := shell_estimate (S k) t w hR hC hB A k (ht k) (hw k) (hcount k)
  have hsum : Summable (fun k => ∑ j ∈ S k, |w j|) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hterm hmajor
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hterm hmajor

end
end ManuscriptAudit.Paper10SpectralTailEstimate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper10SpectralTailEstimate.grouped_tail_summable_and_bound
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
