import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

namespace ManuscriptAudit.Paper07

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

end ManuscriptAudit.Paper07

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Paper07.page282_printed_mixed_reciprocal_bound_false,
    ``ManuscriptAudit.Paper07.page282_mixed_reciprocal_lower_bound] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
