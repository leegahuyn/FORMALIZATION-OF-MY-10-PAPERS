import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PolynomialReciprocalPole
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerComplexZeros

/-! Every disk at zero contains genuine singularities of arbitrarily late finite Euler products. -/

namespace ManuscriptAudit.Paper7CommonEulerFinitePoles

open Filter Topology Polynomial Paper7ActualCommonEuler Paper7CommonEulerLocalDecay
open Paper7CommonEulerPointwise Paper7CommonEulerComplexZeros PolynomialReciprocalPole

noncomputable section

def denominatorPolynomial (n : ℕ) : ℂ[X] :=
  ∏ j ∈ Finset.range n, (1 - C (trace j) * X + C (goodPrime j : ℂ) * X^2)

theorem eval_denominatorPolynomial (n : ℕ) (z : ℂ) :
    (denominatorPolynomial n).eval z = ∏ j ∈ Finset.range n, denominator (goodPrime j) (trace j) z := by
  simp only [denominatorPolynomial, eval_prod, eval_add, eval_sub, eval_mul, eval_one, eval_C,
    eval_X, eval_pow, denominator]

theorem denominatorPolynomial_ne_zero (n : ℕ) : denominatorPolynomial n ≠ 0 := by
  intro he
  have h := eval_denominatorPolynomial n 0
  rw [he, eval_zero] at h
  simp [denominator] at h

theorem finite_product_eq_inverse_eval (n : ℕ) (z : ℂ) :
    partialProduct goodPrime trace z n = ((denominatorPolynomial n).eval z)⁻¹ := by
  rw [eval_denominatorPolynomial, partialProduct, Finset.prod_inv_distrib]

theorem finite_product_cannot_extend_at_pole (n : ℕ) {z₀ : ℂ}
    (hz₀ : (denominatorPolynomial n).eval z₀ = 0) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g z₀ ∧
      ∀ᶠ z in 𝓝[{z : ℂ | (denominatorPolynomial n).eval z ≠ 0}] z₀,
        g z = partialProduct goodPrime trace z n := by
  rintro ⟨g,hg,he⟩
  apply no_continuous_reciprocal_extension _ (denominatorPolynomial_ne_zero n) hz₀
  refine ⟨g,hg,?_⟩
  filter_upwards [he] with z hz
  exact hz.trans (finite_product_eq_inverse_eval n z)

theorem eventually_finite_product_has_pole_inside {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∃ z : ℂ, ‖z‖ < r ∧ (denominatorPolynomial (n+1)).eval z = 0 := by
  filter_upwards [eventually_actual_zero_inside hr] with n hn
  obtain ⟨z,hz,he⟩ := hn
  refine ⟨z,hz,?_⟩
  rw [eval_denominatorPolynomial]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self n)) he

end
end ManuscriptAudit.Paper7CommonEulerFinitePoles

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerFinitePoles.eval_denominatorPolynomial,
      ``ManuscriptAudit.Paper7CommonEulerFinitePoles.denominatorPolynomial_ne_zero,
      ``ManuscriptAudit.Paper7CommonEulerFinitePoles.finite_product_eq_inverse_eval,
      ``ManuscriptAudit.Paper7CommonEulerFinitePoles.finite_product_cannot_extend_at_pole,
      ``ManuscriptAudit.Paper7CommonEulerFinitePoles.eventually_finite_product_has_pole_inside] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
