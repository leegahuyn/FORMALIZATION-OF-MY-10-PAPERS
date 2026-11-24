import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace ManuscriptAudit.Paper07

open scoped BigOperators

private noncomputable def reciprocalLinearPolynomial (α : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C α * Polynomial.X

/-- Paper 7, PDF pp. 271, 280 and 282. At the good prime `p = 5` and
`W = 1`, degree `n = 0` permits a weight-zero eigenvalue `α = 1`.
Its reciprocal polynomial is `1 - T`, with a root at radius one.

The spectral example is realized by the constant ℓ-adic coefficient on
`Spec 𝔽₅` for ℓ different from five. Its geometric compactly supported
cohomology is concentrated in degree zero and Frobenius acts there as the
identity. This Lean result proves the local complex polynomial and radius
statement. The geometric realization and the manuscript's global
four-layer coefficient object are separate constructions. -/
theorem page282_printed_mixed_reciprocal_bound_false :
    ¬ (∀ (μ : ℝ) (α u : ℂ), μ ≤ (1 : ℝ) + 0 → α ≠ 0 →
      ‖α‖ = (5 : ℝ) ^ (μ / 2) → u = α⁻¹ →
      (reciprocalLinearPolynomial α).IsRoot u →
      ‖u‖ ≤ (5 : ℝ) ^ (-(((1 : ℝ) + 0) / 2))) := by
  intro hBound
  have hWeight : (0 : ℝ) ≤ 1 + 0 := by norm_num
  have hAbs : ‖(1 : ℂ)‖ = (5 : ℝ) ^ ((0 : ℝ) / 2) := by simp
  have hRoot : (reciprocalLinearPolynomial 1).IsRoot 1 := by
    simp [reciprocalLinearPolynomial, Polynomial.IsRoot]
  have hSmall : (5 : ℝ) ^ (-(((1 : ℝ) + 0) / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hInside := hBound 0 1 1 hWeight one_ne_zero hAbs (by simp) hRoot
  exact (not_le_of_gt hSmall) (by simpa only [norm_one] using hInside)

/-- The printed upper bound on the weight gives a lower bound on the
reciprocal radius. -/
theorem page282_mixed_reciprocal_lower_bound {p μ W n : ℝ} {α : ℂ}
    (hp : 1 ≤ p) (hWeight : μ ≤ W + n) (hα : α ≠ 0)
    (hAbs : ‖α‖ = p ^ (μ / 2)) :
    p ^ (-((W + n) / 2)) ≤ ‖α⁻¹‖ := by
  have hPow : p ^ (μ / 2) ≤ p ^ ((W + n) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hp
      (div_le_div_of_nonneg_right hWeight (by norm_num))
  rw [Real.rpow_neg (zero_le_one.trans hp), norm_inv]
  exact inv_anti₀ (norm_pos_iff.mpr hα) (hAbs.trans_le hPow)

/-- The local Euler factor is holomorphic on the small disk when its
denominator eigenvalues have a common norm bound. The small-disk consequence
survives after correcting the reciprocal-radius inequality. -/
theorem page280_local_rational_factor_holomorphic_small_disk {A B : Type*}
    [Fintype A] [Fintype B] (α : A → ℂ) (β : B → ℂ) {C : ℝ}
    (hC : 0 < C) (hβ : ∀ b, ‖β b‖ ≤ C) :
    DifferentiableOn ℂ
      (fun z : ℂ => (∏ a : A, (1 - α a * z)) / (∏ b : B, (1 - β b * z)))
      (Metric.ball 0 C⁻¹) := by
  classical
  intro z hz
  have hz' : ‖z‖ < C⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hβz (b : B) : ‖β b * z‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right (hβ b) (norm_nonneg z)
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left hz' hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hNonzero (b : B) : 1 - β b * z ≠ 0 := by
    intro hb
    have h := hβz b
    rw [← sub_eq_zero.mp hb, norm_one] at h
    exact (lt_irrefl _) h
  have hLinear (a : ℂ) : DifferentiableAt ℂ (fun w : ℂ => 1 - a * w) z := by
    fun_prop
  have hNum : DifferentiableAt ℂ (fun w : ℂ => ∏ a : A, (1 - α a * w)) z :=
    DifferentiableAt.fun_finsetProd (fun a _ => hLinear (α a))
  have hDen : DifferentiableAt ℂ (fun w : ℂ => ∏ b : B, (1 - β b * w)) z :=
    DifferentiableAt.fun_finsetProd (fun b _ => hLinear (β b))
  have hDenNonzero : (∏ b : B, (1 - β b * z)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => hNonzero b)
  exact (hNum.div hDen hDenNonzero).differentiableWithinAt

end ManuscriptAudit.Paper07

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Paper07.page282_printed_mixed_reciprocal_bound_false,
    ``ManuscriptAudit.Paper07.page282_mixed_reciprocal_lower_bound,
    ``ManuscriptAudit.Paper07.page280_local_rational_factor_holomorphic_small_disk] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

