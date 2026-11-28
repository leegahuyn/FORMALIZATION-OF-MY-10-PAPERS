import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLaplaceTerm

/-! Agreement of the manuscript Dirichlet series with its logarithmic Laplace transform. -/

namespace ManuscriptAudit.Paper8OddCrossDirichletLaplace

open Filter MeasureTheory Set
open Paper8BoundaryLaplace Paper8OddCrossAbelObstruction Paper8OddCrossCuspCutoff
open Paper8OddCrossLaplaceTerm Paper8OddCrossZetaFactorization
open scoped Nat

noncomputable section

theorem tsum_crossLaplaceTerm (w : ℂ) (t : ℝ) :
    (∑' j, crossLaplaceTerm w j t) = crossLogarithmicStep t * Complex.exp (-w * (t : ℂ)) := by
  let N := ⌊Real.exp t⌋₊
  have hSupport (j : ℕ) (hj : j ∉ Finset.range N) : crossLaplaceTerm w j t = 0 := by
    apply Set.indicator_of_notMem
    intro h
    exact hj (Finset.mem_range.mpr ((logarithmicThreshold_le_iff j t).mp h))
  rw [tsum_eq_sum (s := Finset.range N) hSupport]
  change _ = orderedCrossCutoff N * _
  rw [orderedCrossCutoff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact Set.indicator_of_mem ((logarithmicThreshold_le_iff j t).mpr (Finset.mem_range.mp hj)) _

private theorem summable_crossLaplace_norm_integral {w : ℂ} (hw : 1 < w.re) :
    Summable (fun j => ∫ t in Ioi (0 : ℝ), ‖crossLaplaceTerm w j t‖) := by
  have hp : 0 < w.re := zero_lt_one.trans hw
  have hMajorant : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-w.re))) :=
    ((Real.summable_one_div_nat_add_rpow 1 w.re).2 hw).congr (fun j => by
      rw [abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1), one_div,
        ← Real.rpow_neg (by positivity : 0 ≤ (j : ℝ) + 1), Nat.cast_add, Nat.cast_one])
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg (fun _ => norm_nonneg _))
    (fun j => ?_) (hMajorant.mul_left (1 / w.re))
  rw [crossLaplaceTerm_norm_integral hp]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (norm_crossRaw_le_one j) hp.le)
    (by positivity)

theorem crossAbelShiftedZeta_eq_shifted_series {w : ℂ} (hw : 1 < w.re) :
    crossAbelShiftedZeta w =
      ∑' j : ℕ, (2 : ℂ) ^ (-(w + 1)) * (crossRaw j * (((j + 1 : ℕ) : ℂ) ^ (-w))) := by
  have hp : 0 < w.re := zero_lt_one.trans hw
  have hn : w ≠ 0 := by intro h; simp [h] at hp
  have hSum : HasSum (fun j => ∫ t in Ioi (0 : ℝ), crossLaplaceTerm w j t)
      (∫ t in Ioi (0 : ℝ), ∑' j, crossLaplaceTerm w j t) :=
    hasSum_integral_of_summable_integral_norm (crossLaplaceTerm_integrable hp)
      (summable_crossLaplace_norm_integral hw)
  have hEq := hSum.tsum_eq
  simp_rw [tsum_crossLaplaceTerm, crossLaplaceTerm_integral hp,
    div_eq_mul_inv, ← mul_assoc] at hEq
  rw [tsum_mul_right] at hEq
  change _ = boundaryLaplace crossLogarithmicStep w at hEq
  rw [crossAbelShiftedZeta, ← hEq, tsum_mul_left]
  field_simp [hn] <;> ring

private theorem shifted_modulus_factor (w : ℂ) {k : ℕ} (hk : 0 < k) :
    crossModulusFactor ((w + 1) / 2) (2 * (k : ℝ)) =
      (2 : ℂ) ^ (-(w + 1)) * (k : ℂ) ^ (-(w + 1)) := by
  let c : ℝ := 2 * (k : ℝ)
  have hc : 0 < c := by unfold c; positivity
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hcC : (((c ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  have hA : Complex.log (((c ^ 2)⁻¹ : ℝ) : ℂ) = -(2 : ℂ) * ((Real.log c : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (by positivity : 0 ≤ (c ^ 2)⁻¹), Real.log_inv, Real.log_pow]
    push_cast <;> norm_num
  have hB : ((Real.log c : ℝ) : ℂ) = Complex.log 2 + Complex.log (k : ℂ) := by
    unfold c
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (k : ℝ) ≠ 0), Complex.ofReal_add]
    rw [Complex.ofReal_log (by norm_num : 0 ≤ (2 : ℝ)),
      Complex.ofReal_log (Nat.cast_nonneg k), Complex.ofReal_natCast] <;> norm_num
  change (((c ^ 2)⁻¹ : ℝ) : ℂ) ^ ((w + 1) / 2) = _
  rw [Complex.cpow_def_of_ne_zero hcC, Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero hkC, hA, hB, ← Complex.exp_add]
  congr 1
  ring

theorem oddCrossZetaTerm_eq_shifted (w : ℂ) (j : ℕ) :
    oddCrossZetaTerm ((w + 1) / 2) j =
      (2 : ℂ) ^ (-(w + 1)) * (crossRaw j * (((j + 1 : ℕ) : ℂ) ^ (-w))) := by
  have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [oddCrossZetaTerm, shifted_modulus_factor w (Nat.succ_pos j)]
  have hP : ((j + 1 : ℕ) : ℂ) ^ (-(w + 1)) =
      (((j + 1 : ℕ) : ℂ)⁻¹) * (((j + 1 : ℕ) : ℂ) ^ (-w)) := by
    rw [show -(w + 1) = -1 + -w by ring, Complex.cpow_add (-1) (-w) hj, Complex.cpow_neg_one]
  rw [hP, crossRaw, div_eq_mul_inv]
  ring

theorem crossAbelShiftedZeta_eq_oddCrossZeta {w : ℂ} (hw : 1 < w.re) :
    crossAbelShiftedZeta w = ∑' j, oddCrossZetaTerm ((w + 1) / 2) j := by
  rw [crossAbelShiftedZeta_eq_shifted_series hw]
  exact tsum_congr (fun j => (oddCrossZetaTerm_eq_shifted w j).symm)

end
end ManuscriptAudit.Paper8OddCrossDirichletLaplace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossDirichletLaplace.tsum_crossLaplaceTerm,
      ``ManuscriptAudit.Paper8OddCrossDirichletLaplace.oddCrossZetaTerm_eq_shifted,
      ``ManuscriptAudit.Paper8OddCrossDirichletLaplace.crossAbelShiftedZeta_eq_oddCrossZeta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
