import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import PrimalitySheafVerification.ManuscriptAudit.Paper7FiniteEulerSimpleRoots

/-! Exact nonzero first principal-part coefficient of each finite Euler pole. -/

namespace ManuscriptAudit.Paper7FiniteEulerPoleResidue

open Filter Polynomial Paper7ActualCommonEuler Paper7CommonEulerPointwise
open Paper7CommonEulerFinitePoles Paper7FiniteEulerSimpleRoots
open scoped Topology

theorem actual_finite_euler_simple_pole (n : ℕ) {z₀ : ℂ}
    (h₀ : (denominatorPolynomial n).eval z₀ = 0) :
    ((denominatorPolynomial n).derivative.eval z₀)⁻¹ ≠ 0 ∧
    Tendsto (fun z : ℂ => (z-z₀) * partialProduct goodPrime trace z n)
      (𝓝[≠] z₀) (𝓝 (((denominatorPolynomial n).derivative.eval z₀)⁻¹)) := by
  have hd := denominator_root_is_simple n h₀
  refine ⟨inv_ne_zero hd, ?_⟩
  have h := (((denominatorPolynomial n).hasDerivAt z₀).tendsto_slope).inv₀ hd
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro z
  change (slope (fun x : ℂ => (denominatorPolynomial n).eval x) z₀ z)⁻¹ =
    (z-z₀) * partialProduct goodPrime trace z n
  rw [finite_product_eq_inverse_eval n z, slope_def_field, h₀, sub_zero, inv_div, div_eq_mul_inv]

end ManuscriptAudit.Paper7FiniteEulerPoleResidue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper7FiniteEulerPoleResidue.actual_finite_euler_simple_pole
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
