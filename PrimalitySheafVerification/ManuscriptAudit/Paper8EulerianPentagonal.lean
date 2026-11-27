import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrence

/-! Iterating the Eulerian recurrence gives the genuine pentagonal series. -/

namespace ManuscriptAudit.Paper8EulerianPentagonal

open Filter Paper8EulerianRecurrence
open scoped Topology

noncomputable section

def exponent (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (3 * j + 2)

def pentagonalTerm (q : ℝ) (n : ℕ) : ℝ := q ^ exponent n * (1 - q ^ (2 * n + 1))

def pentagonalSeries (q : ℝ) : ℝ := ∑' n : ℕ, pentagonalTerm q n

private def residual (q : ℝ) (n : ℕ) : ℝ := q ^ exponent n * H q (q ^ n)

theorem exponent_succ (n : ℕ) : exponent (n + 1) = exponent n + (3 * n + 2) := by
  simp only [exponent, Finset.sum_range_succ]

theorem twice_exponent (n : ℕ) : 2 * exponent n = n * (3 * n + 1) := by
  induction n with
  | zero => simp [exponent]
  | succ n ih => rw [exponent_succ, mul_add, ih]; ring

theorem self_le_exponent (n : ℕ) : n ≤ exponent n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => rw [exponent_succ]; omega

private theorem pow_le_one {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    q ^ n ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hq h₁ n

private theorem residual_step {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (n : ℕ) :
    residual q n = pentagonalTerm q n + residual q (n + 1) := by
  have hSq : (q ^ n) ^ 2 * q = q ^ (2 * n + 1) := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_succ]
  have hCube : (q ^ n) ^ 3 * q ^ 2 = q ^ (3 * n + 2) := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_add q (3 * n) 2]
  have hNext : q ^ n * q = q ^ (n + 1) := (pow_succ q n).symm
  unfold residual pentagonalTerm
  rw [H_recurrence hq h₁ (pow_nonneg hq n) (pow_le_one hq h₁.le n),
    hSq, hCube, hNext, exponent_succ, pow_add q (exponent n) (3 * n + 2)]
  ring

private theorem sum_range_add_residual {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, pentagonalTerm q n) + residual q N = H q 1 := by
  induction N with
  | zero => simp [residual, exponent]
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, ← residual_step hq h₁ N, ih]

theorem pentagonalTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    0 ≤ pentagonalTerm q n :=
  mul_nonneg (pow_nonneg hq _) (sub_nonneg.mpr (pow_le_one hq h₁ _))

theorem pentagonalTerm_le_geom {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    pentagonalTerm q n ≤ q ^ n := by
  unfold pentagonalTerm
  calc
    _ ≤ q ^ exponent n * 1 := mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg hq _))
      (pow_nonneg hq _)
    _ ≤ _ := by
      simpa only [mul_one] using pow_le_pow_of_le_one hq h₁ (self_le_exponent n)

theorem pentagonalTerm_summable {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    Summable (pentagonalTerm q) :=
  Summable.of_nonneg_of_le (pentagonalTerm_nonneg hq h₁.le) (pentagonalTerm_le_geom hq h₁.le)
    (summable_geometric_of_lt_one hq h₁)

private theorem residual_tendsto_zero {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    Tendsto (residual q) atTop (𝓝 0) := by
  have hMajorant : Tendsto (fun n : ℕ => q ^ n * (1 - q)⁻¹) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq h₁).mul_const (1 - q)⁻¹
  refine squeeze_zero_norm (fun n => ?_) hMajorant
  rw [residual, norm_mul, Real.norm_of_nonneg (pow_nonneg hq (exponent n)), Real.norm_eq_abs]
  exact mul_le_mul (pow_le_pow_of_le_one hq h₁.le (self_le_exponent n))
    (H_abs_le_geometric hq h₁ (pow_nonneg hq n) (pow_le_one hq h₁.le n))
    (abs_nonneg _) (pow_nonneg hq n)

theorem H_one_eq_pentagonalSeries {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    H q 1 = pentagonalSeries q := by
  have hLimit : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, pentagonalTerm q n) + residual q N)
      atTop (𝓝 (pentagonalSeries q)) := by
    simpa only [add_zero, pentagonalSeries] using
      (pentagonalTerm_summable hq h₁).tendsto_sum_tsum_nat.add (residual_tendsto_zero hq h₁)
  have hConst : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, pentagonalTerm q n) + residual q N)
      atTop (𝓝 (H q 1)) := by
    simp_rw [sum_range_add_residual hq h₁]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hConst hLimit

end
end ManuscriptAudit.Paper8EulerianPentagonal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianPentagonal.twice_exponent,
      ``ManuscriptAudit.Paper8EulerianPentagonal.pentagonalTerm_summable,
      ``ManuscriptAudit.Paper8EulerianPentagonal.H_one_eq_pentagonalSeries] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
