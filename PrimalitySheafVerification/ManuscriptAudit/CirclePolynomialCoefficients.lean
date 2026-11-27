import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Native Cauchy coefficients of complex polynomials and uniform circle limits. -/

namespace ManuscriptAudit.CirclePolynomialCoefficients

open Filter Metric Set
open scoped Topology

noncomputable section

private def kernel (m : ℕ) (z : ℂ) : ℂ := z ^ (-(m : ℤ) - 1)

private theorem sphere_norm {R : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖z‖ = R := by
  simpa only [Metric.mem_sphere, dist_zero_right] using hz

private theorem sphere_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) : z ≠ 0 := by
  intro he
  have h := sphere_norm hz
  rw [he, norm_zero] at h
  exact hR.ne' h.symm

private theorem continuousOn_kernel (m : ℕ) {R : ℝ} (hR : 0 < R) :
    ContinuousOn (kernel m) (sphere (0 : ℂ) R) :=
  continuous_id.continuousOn.zpow₀ _ (fun _ hz => Or.inl (sphere_ne_zero hR hz))

def coefficient (f : ℂ → ℂ) (R : ℝ) (m : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, R), kernel m z * f z

theorem coefficient_polynomial_eval (p : Polynomial ℂ) {R : ℝ} (hR : 0 < R) (m : ℕ) :
    coefficient p.eval R m = p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hpC : ContinuousOn p.eval (sphere (0 : ℂ) R) :=
      fun _ _ => p.differentiableAt.continuousAt.continuousWithinAt
    have hqC : ContinuousOn q.eval (sphere (0 : ℂ) R) :=
      fun _ _ => q.differentiableAt.continuousAt.continuousWithinAt
    simp only [coefficient, Polynomial.eval_add, mul_add, Polynomial.coeff_add] at hp hq ⊢
    rw [circleIntegral.integral_add
      (((continuousOn_kernel m hR).mul hpC).circleIntegrable hR.le)
      (((continuousOn_kernel m hR).mul hqC).circleIntegrable hR.le), mul_add, hp, hq]
  | monomial k a =>
    have hEq : Set.EqOn (fun z : ℂ => kernel m z * (a * z ^ k))
        (fun z => a * z ^ ((k : ℤ) - (m : ℤ) - 1)) (sphere (0 : ℂ) R) := by
      intro z hz
      calc
        kernel m z * (a * z ^ k) =
            a * (z ^ (-(m : ℤ) - 1) * z ^ (k : ℤ)) := by
          simp only [kernel, zpow_natCast]
          ring
        _ = a * z ^ ((k : ℤ) - (m : ℤ) - 1) := by
          rw [← zpow_add₀ (sphere_ne_zero hR hz)]
          congr 2 <;> ring
    simp only [coefficient, Polynomial.eval_monomial]
    rw [circleIntegral.integral_congr hR.le hEq, circleIntegral.integral_const_mul]
    by_cases h : k = m
    · subst k
      have hPow : ((m : ℤ) - (m : ℤ) - 1) = -1 := by ring
      have hI : (∮ z in C(0, R), z ^ (-1 : ℤ)) = 2 * (Real.pi : ℂ) * Complex.I := by
        simpa only [sub_zero, zpow_neg_one] using circleIntegral.integral_sub_center_inv 0 hR.ne'
      have hNZ : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
      rw [hPow, hI]
      simp only [Polynomial.coeff_monomial, if_pos rfl]
      rw [mul_comm a _, ← mul_assoc, inv_mul_cancel₀ hNZ, one_mul]
    · have hne : ((k : ℤ) - (m : ℤ) - 1) ≠ -1 := by omega
      have hI : (∮ z in C(0, R), z ^ ((k : ℤ) - (m : ℤ) - 1)) = 0 := by
        simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hne (0 : ℂ) 0 R
      simp [hI, Polynomial.coeff_monomial, Ne.symm h]

theorem coefficient_tendsto_uniformly {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (m : ℕ)
    (hC : ∀ n, ContinuousOn (f n) (sphere (0 : ℂ) R))
    (h : TendstoUniformlyOn f g atTop (sphere (0 : ℂ) R)) :
    Tendsto (fun n => coefficient (f n) R m) atTop (𝓝 (coefficient g R m)) := by
  have hW : TendstoUniformlyOn (fun n z => kernel m z * f n z)
      (fun z => kernel m z * g z) atTop (sphere (0 : ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    let M : ℝ := max 1 (R ^ (-(m : ℤ) - 1))
    have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
    filter_upwards [h (ε / M) (div_pos hε hM)] with n hn z hz
    have hb : ‖kernel m z‖ ≤ M := by
      rw [kernel, norm_zpow, sphere_norm hz]
      exact le_max_right _ _
    simp only [dist_eq_norm, ← mul_sub, norm_mul]
    have hn' := hn z hz
    rw [dist_eq_norm] at hn'
    calc
      ‖kernel m z‖ * _ ≤ M * _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left hn' hM
      _ = ε := by field_simp
  have hwc (n : ℕ) : ContinuousOn (fun z => kernel m z * f n z) (sphere (0 : ℂ) R) :=
    (continuousOn_kernel m hR).mul (hC n)
  have hI := hW.tendsto_circleIntegral_of_continuousOn hR.le (Filter.Eventually.of_forall hwc)
  exact tendsto_const_nhds.mul hI

end
end ManuscriptAudit.CirclePolynomialCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CirclePolynomialCoefficients.coefficient_polynomial_eval,
      ``ManuscriptAudit.CirclePolynomialCoefficients.coefficient_tendsto_uniformly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
