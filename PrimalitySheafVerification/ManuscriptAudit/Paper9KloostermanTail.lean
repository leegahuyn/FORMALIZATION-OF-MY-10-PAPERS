import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The printed Kloosterman and Bessel size bounds do not control the modulus sum

Physical pp. 431–432 estimate the diagonal c-series using a
c^(1/2+ε) gcd^(1/2) bound and a bounded small-x kernel.
The model below satisfies both size inequalities for all m,c and
has a smooth kernel on x>0. Its ordered diagonal sums are unbounded
already at m=1. This is a counterexample to the inference from the
bounds alone, with no identification with the actual Kloosterman sums.
-/

namespace ManuscriptAudit.Paper9KloostermanTail

open scoped ContDiff

noncomputable section

def coefficient (m c : ℕ) : ℝ :=
  if m = 1 then Real.sqrt c else 0

def kernel (x : ℝ) : ℝ := 1 / (1 + x)

def summand (m c : ℕ) : ℝ :=
  coefficient m c / (c : ℝ) * kernel (4 * Real.pi * (m : ℝ) / (c : ℝ))

theorem coefficient_envelope (m : ℕ) {c : ℕ} (hc : 0 < c) {ε : ℝ} (hε : 0 ≤ ε) :
    |coefficient m c| ≤ (c : ℝ) ^ (1 / 2 + ε) * Real.sqrt (Nat.gcd m c) := by
  by_cases hm : m = 1
  · subst m
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (show 1 ≤ c from hc)
    simp only [coefficient, if_pos rfl, abs_of_nonneg (Real.sqrt_nonneg _),
      Nat.gcd_one_left, Nat.cast_one, Real.sqrt_one, mul_one]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
  · rw [coefficient, if_neg hm, abs_zero]
    positivity

theorem kernel_smooth : ContDiffOn ℝ ∞ kernel (Set.Ioi (0 : ℝ)) := by
  unfold kernel
  have h : ContDiff ℝ ∞ (fun x : ℝ => 1 + x) := contDiff_const.add contDiff_id
  exact (contDiff_const (c := (1 : ℝ))).contDiffOn.div h.contDiffOn (fun x hx => by
    exact (add_pos zero_lt_one (Set.mem_Ioi.mp hx)).ne')

theorem kernel_small_envelope {x : ℝ} (hx : 0 < x) : |kernel x| ≤ 1 := by
  unfold kernel
  have hp : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hp]
  linarith

theorem kernel_large_envelope {x : ℝ} (hx : 1 ≤ x) :
    |kernel x| ≤ 1 / Real.sqrt x := by
  have hp : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  unfold kernel
  rw [abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hp) (hs.trans (by linarith))

private theorem summand_one_nonneg (c : ℕ) : 0 ≤ summand 1 c := by
  simp only [summand, coefficient, if_pos rfl, kernel, Nat.cast_one]
  positivity

theorem summand_one_tail_ge_harmonic {c : ℕ} (hc : 13 ≤ c) :
    (1 / 2 : ℝ) * (1 / (c : ℝ)) ≤ summand 1 c := by
  have hC : (13 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hc0 : 0 < (c : ℝ) := by linarith
  have hWidth : 4 * Real.pi / (c : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hc0).2
    linarith [Real.pi_lt_d2]
  have hSqrt : 1 ≤ Real.sqrt (c : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hFactor : (1 : ℝ) / 2 ≤ kernel (4 * Real.pi / (c : ℝ)) := by
    unfold kernel
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  simp only [summand, coefficient, if_pos rfl, Nat.cast_one, mul_one]
  calc
    _ = 1 / (c : ℝ) * (1 / 2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hSqrt hc0.le) hFactor (by norm_num) (by positivity)

theorem diagonal_not_summable : ¬ Summable (fun n : ℕ => summand 1 (n + 1)) := by
  intro h
  have hTail : Summable (fun n : ℕ => summand 1 (n + 13)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 12).2 h
  have hH : Summable (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n + 13 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => summand_one_tail_ge_harmonic (by omega : 13 ≤ n + 13)) hTail
  have hStd : Summable (fun n : ℕ => 1 / ((n + 13 : ℕ) : ℝ)) := by
    refine (hH.mul_left 2).congr fun n => ?_
    ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 13).mp hStd)

theorem ordered_diagonal_partial_sums_unbounded (B : ℝ) :
    ∃ N : ℕ, B < ∑ n ∈ Finset.range N, summand 1 (n + 1) := by
  by_contra! h
  exact diagonal_not_summable (summable_of_sum_range_le (fun n => summand_one_nonneg (n + 1)) h)

end
end ManuscriptAudit.Paper9KloostermanTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9KloostermanTail.coefficient_envelope,
      ``ManuscriptAudit.Paper9KloostermanTail.kernel_smooth,
      ``ManuscriptAudit.Paper9KloostermanTail.kernel_small_envelope,
      ``ManuscriptAudit.Paper9KloostermanTail.kernel_large_envelope,
      ``ManuscriptAudit.Paper9KloostermanTail.diagonal_not_summable,
      ``ManuscriptAudit.Paper9KloostermanTail.ordered_diagonal_partial_sums_unbounded] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
