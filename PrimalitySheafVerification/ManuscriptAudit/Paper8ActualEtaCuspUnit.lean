import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# The actual eta cusp unit and leading width factor

The Dedekind eta product after a positive integral width rescaling is
an explicit exponential times a holomorphic q-disc unit with value one
at q=0. The elementary order comparison records why a width less than
24 leaves no negative integral order after the common eta factor.
-/

namespace ManuscriptAudit.Paper8ActualEtaCuspUnit

open Function.Periodic Set

noncomputable section

def widthUnit (w : ℕ) (q : ℂ) : ℂ :=
  ∏' n : ℕ, 1 - (q ^ w) ^ (n + 1)

theorem widthUnit_at_zero {w : ℕ} (hw : 0 < w) :
    widthUnit w 0 = 1 := by
  simp [widthUnit, zero_pow hw.ne']

theorem widthUnit_differentiableOn {w : ℕ} (hw : 0 < w) :
    DifferentiableOn ℂ (widthUnit w) (Metric.ball (0 : ℂ) 1) := by
  have hPow : Differentiable ℂ (fun q : ℂ => q ^ w) := by fun_prop
  unfold widthUnit
  refine ModularForm.differentiableOn_tprod_one_sub_pow.comp hPow.differentiableOn ?_
  intro q hq
  have hN : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  simpa [Metric.mem_ball, dist_zero_right, norm_pow] using
    (pow_lt_one₀ (norm_nonneg q) hN hw.ne')

theorem eta_rescaled_cusp_factorization (w : ℕ) (z : ℂ) :
    ModularForm.eta ((w : ℂ) * z) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * z / 24) *
        widthUnit w (qParam 1 z) := by
  have hQ : qParam 1 ((w : ℂ) * z) = qParam 1 z ^ w := by
    unfold qParam
    simp only [Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
    congr 1
    ring
  unfold ModularForm.eta widthUnit
  rw [show qParam 24 ((w : ℂ) * z) =
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * z / 24) by
      unfold qParam
      norm_num <;> congr 1 <;> ring]
  simp only [ModularForm.eta_q, hQ]

theorem integral_order_nonnegative_of_small_width {w : ℕ} {a : ℤ}
    (hw : w < 24) (h : 0 ≤ (w : ℝ) / 24 + (a : ℝ)) : 0 ≤ a := by
  have hw' : (w : ℝ) < 24 := by exact_mod_cast hw
  by_contra ha
  have haI : a ≤ -1 := by omega
  have haR : (a : ℝ) ≤ -1 := by exact_mod_cast haI
  linarith

end
end ManuscriptAudit.Paper8ActualEtaCuspUnit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaCuspUnit.widthUnit_at_zero,
      ``ManuscriptAudit.Paper8ActualEtaCuspUnit.widthUnit_differentiableOn,
      ``ManuscriptAudit.Paper8ActualEtaCuspUnit.eta_rescaled_cusp_factorization,
      ``ManuscriptAudit.Paper8ActualEtaCuspUnit.integral_order_nonnegative_of_small_width] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
