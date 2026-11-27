import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinarySums

/-! An exact finite telescope gives the ordinary exterior tail recurrence. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryTelescope

open Filter Paper8ExteriorOrdinaryProduct Paper8ExteriorOrdinarySums
open scoped Topology

noncomputable section

private def Y (q a : ℝ) (n : ℕ) : ℝ := U q (a * q ^ n)

private def Z (q a : ℝ) (n : ℕ) : ℝ := U q ((a * q)⁻¹ * q ^ n)

private def V (q a : ℝ) (n : ℕ) : ℝ := Y q a n * Z q a n

private theorem y_step {q : ℝ} (hq : 0 < q) (h₁ : q < 1) (a : ℝ) (n : ℕ) :
    Y q a n = (1 + a * q * q ^ n) * Y q a (n + 1) := by
  have hArg : (a * q ^ n) * q = a * q ^ (n + 1) := by rw [pow_succ q n, mul_assoc]
  have hCoeff : (a * q ^ n) * q = a * q * q ^ n := by ring
  calc
    _ = (1 + (a * q ^ n) * q) * U q ((a * q ^ n) * q) := U_step hq.le h₁ _
    _ = _ := congrArg₂ (· * ·) (congrArg (fun x : ℝ => 1 + x) hCoeff) (congrArg (U q) hArg)

private theorem z_step {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (n : ℕ) :
    Z q a n = (1 + a⁻¹ * q ^ n) * Z q a (n + 1) := by
  have hArg : ((a * q)⁻¹ * q ^ n) * q = (a * q)⁻¹ * q ^ (n + 1) := by
    rw [pow_succ q n, mul_assoc]
  have hCoeff : ((a * q)⁻¹ * q ^ n) * q = a⁻¹ * q ^ n := by
    calc
      _ = ((a * q)⁻¹ * q) * q ^ n := by ring
      _ = _ := by rw [inverse_parameter_mul hq ha]
  calc
    _ = (1 + ((a * q)⁻¹ * q ^ n) * q) * U q (((a * q)⁻¹ * q ^ n) * q) :=
      U_step hq.le h₁ _
    _ = _ := congrArg₂ (· * ·) (congrArg (fun x : ℝ => 1 + x) hCoeff) (congrArg (U q) hArg)

private theorem JTerm_YZ {q a : ℝ} (hq : 0 < q) (ha : 0 < a) (n : ℕ) :
    JTerm q a n = q ^ n * Y q a n * Z q a (n + 1) := by
  have hZ : Z q a (n + 1) = U q (a⁻¹ * q ^ n) := by
    unfold Z
    congr 1
    rw [pow_succ' q n, ← mul_assoc, inverse_parameter_mul hq ha]
  rw [JTerm, Y, hZ]

private theorem JTerm_shift_YZ (q a : ℝ) (n : ℕ) :
    JTerm q (a * q) n = q ^ n * Y q a (n + 1) * Z q a n := by
  simp only [JTerm, Y, Z, pow_succ' q n, mul_assoc]

private theorem factor_telescope (a q r y z : ℝ) (ha : a ≠ 0) :
    r * ((1 + a * q * r) * y) * z - a ^ 4 * q ^ 2 * (r * y * ((1 + a⁻¹ * r) * z)) =
      a * (1 - a ^ 2 * q) * (((1 + a * q * r) * y) * ((1 + a⁻¹ * r) * z) - y * z) := by
  field_simp [ha] <;> ring

theorem JTerm_difference {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (n : ℕ) :
    JTerm q a n - a ^ 4 * q ^ 2 * JTerm q (a * q) n =
      a * (1 - a ^ 2 * q) * (V q a n - V q a (n + 1)) := by
  rw [JTerm_YZ hq ha n, JTerm_shift_YZ q a n, V, V,
    y_step hq h₁ a n, z_step hq h₁ ha n]
  exact factor_telescope a q (q ^ n) (Y q a (n + 1)) (Z q a (n + 1)) ha.ne'

private theorem V_zero {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) :
    V q a 0 = (1 + a⁻¹) * W q a := by
  simp only [V, Y, Z, pow_zero, mul_one, W]
  rw [U_step hq.le h₁ ((a * q)⁻¹), inverse_parameter_mul hq ha]
  ring

private theorem V_tendsto_one {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) :
    Tendsto (V q a) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => U q (a * q ^ n) * U q ((a * q)⁻¹ * q ^ n)) atTop (𝓝 1)
  simpa only [one_mul] using (U_tail_tendsto_one hq.le h₁ ha.le).mul
    (U_tail_tendsto_one hq.le h₁ (inv_nonneg.mpr (mul_nonneg ha.le hq.le)))

private theorem finite_telescope (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f n - f (n + 1))) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

theorem J_recurrence {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) :
    J q a - a ^ 4 * q ^ 2 * J q (a * q) =
      (1 - a ^ 2 * q) * ((1 + a) * W q a - a) := by
  let diff (n : ℕ) : ℝ := JTerm q a n - a ^ 4 * q ^ 2 * JTerm q (a * q) n
  have hJa := J_summable hq.le h₁ ha.le
  have hJaq := J_summable hq.le h₁ (mul_nonneg ha.le hq.le)
  have hSum : Summable diff := hJa.sub (hJaq.mul_left (a ^ 4 * q ^ 2))
  have hTsum : (∑' n : ℕ, diff n) = J q a - a ^ 4 * q ^ 2 * J q (a * q) := by
    change tsum (fun n => JTerm q a n - a ^ 4 * q ^ 2 * JTerm q (a * q) n) = _
    rw [hJa.tsum_sub (hJaq.mul_left (a ^ 4 * q ^ 2)), hJaq.tsum_mul_left] <;> rfl
  have hPartial (N : ℕ) :
      (∑ n ∈ Finset.range N, diff n) = a * (1 - a ^ 2 * q) * (V q a 0 - V q a N) := by
    change (∑ n ∈ Finset.range N, (JTerm q a n - a ^ 4 * q ^ 2 * JTerm q (a * q) n)) = _
    simp_rw [JTerm_difference hq h₁ ha]
    rw [← Finset.mul_sum, finite_telescope]
  have hRaw := hSum.tendsto_sum_tsum_nat
  rw [hTsum] at hRaw
  have hTel : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, diff n) atTop
      (𝓝 (a * (1 - a ^ 2 * q) * (V q a 0 - 1))) := by
    simp_rw [hPartial]
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub (V_tendsto_one hq h₁ ha))
  have hEq := tendsto_nhds_unique hRaw hTel
  rw [hEq, V_zero hq h₁ ha]
  field_simp [ha.ne'] <;> ring

end
end ManuscriptAudit.Paper8ExteriorOrdinaryTelescope

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryTelescope.JTerm_difference,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryTelescope.J_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
