import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombMultiplier
import PrimalitySheafVerification.ManuscriptAudit.SmoothGaugeCurvature

/-!
# Which scalar multipliers preserve local Coulomb gauge

On the hyperbolic chart the two coordinate covectors are co-closed.
The product rule shows that preserving co-closedness for all smooth
local forms forces both coordinate derivatives of the scalar multiplier
to vanish at the point. Vanishing of those two derivatives also suffices.
-/

namespace ManuscriptAudit.Paper10CoulombProductRule

open Paper10CoulombMultiplier
open SmoothGaugeCurvature (partialX partialY)

noncomputable section

/-- Multiplication of the two covector coefficients by a scalar function. -/
def scaleOneForm (μ : ScalarField) (a : OneForm) : OneForm :=
  fun x y => (μ x y * (a x y).1, μ x y * (a x y).2)

theorem codifferential_eq_coordinateDivergence (a : OneForm) (x y : ℝ) :
    codifferential a x y =
      -(y ^ 2 * (deriv (fun t => (a t y).1) x + deriv (fun t => (a x t).2) y)) := by
  change -(y ^ 2 * (deriv (fun t => (a t y).1) x -
    deriv (-(fun t => (a x t).2)) y)) = _
  rw [deriv.neg, sub_neg_eq_add]

/-- The multiplier differentiates once in each of the two coframe directions. -/
theorem codifferential_scale
    (μ : ScalarField) (a : OneForm) (x y : ℝ)
    (hμx : DifferentiableAt ℝ (fun t => μ t y) x)
    (hμy : DifferentiableAt ℝ (μ x) y)
    (hax : DifferentiableAt ℝ (fun t => (a t y).1) x)
    (hay : DifferentiableAt ℝ (fun t => (a x t).2) y) :
    codifferential (scaleOneForm μ a) x y =
      μ x y * codifferential a x y -
        y ^ 2 * (partialX μ x y * (a x y).1 + partialY μ x y * (a x y).2) := by
  have hx := deriv_mul hμx hax
  have hy := deriv_mul hμy hay
  change deriv (fun t => μ t y * (a t y).1) x = _ at hx
  change deriv (fun t => μ x t * (a x t).2) y = _ at hy
  rw [codifferential_eq_coordinateDivergence, codifferential_eq_coordinateDivergence a]
  unfold scaleOneForm partialX partialY
  rw [hx, hy]
  ring

/-- A local test using one-forms whose coordinate divergence vanishes
throughout the chart. Only the indicated first partial derivatives are
needed at the evaluation point. -/
def PreservesCoclosedAt (μ : ScalarField) (x y : ℝ) : Prop :=
  ∀ a : OneForm, DifferentiableAt ℝ (fun t => (a t y).1) x →
    DifferentiableAt ℝ (fun t => (a x t).2) y →
    (∀ s t, codifferential a s t = 0) →
    codifferential (scaleOneForm μ a) x y = 0

private theorem constant_codifferential (u : ℝ × ℝ) (x y : ℝ) :
    codifferential (fun _ _ => u) x y = 0 := by
  rw [codifferential_eq_coordinateDivergence]
  simp

private theorem scale_dx (μ : ScalarField) (x y : ℝ) :
    codifferential (scaleOneForm μ (fun _ _ => (1, 0))) x y =
      -(y ^ 2 * partialX μ x y) := by
  rw [codifferential_eq_coordinateDivergence]
  simp [scaleOneForm, partialX]

private theorem scale_dy (μ : ScalarField) (x y : ℝ) :
    codifferential (scaleOneForm μ (fun _ _ => (0, 1))) x y =
      -(y ^ 2 * partialY μ x y) := by
  rw [codifferential_eq_coordinateDivergence]
  simp [scaleOneForm, partialY]

theorem preservesCoclosedAt_iff_partials_zero
    (μ : ScalarField) (x y : ℝ) (hy : 0 < y)
    (hμx : DifferentiableAt ℝ (fun t => μ t y) x)
    (hμy : DifferentiableAt ℝ (μ x) y) :
    PreservesCoclosedAt μ x y ↔ partialX μ x y = 0 ∧ partialY μ x y = 0 := by
  constructor
  · intro h
    have hx := h (fun _ _ => (1, 0)) (differentiableAt_const (1 : ℝ))
      (differentiableAt_const (0 : ℝ)) (constant_codifferential (1, 0))
    have hy' := h (fun _ _ => (0, 1)) (differentiableAt_const (0 : ℝ))
      (differentiableAt_const (1 : ℝ)) (constant_codifferential (0, 1))
    rw [scale_dx] at hx
    rw [scale_dy] at hy'
    exact ⟨(mul_eq_zero.mp (neg_eq_zero.mp hx)).resolve_left (pow_ne_zero _ hy.ne'),
      (mul_eq_zero.mp (neg_eq_zero.mp hy')).resolve_left (pow_ne_zero _ hy.ne')⟩
  · intro h a hax hay ha
    rw [codifferential_scale μ a x y hμx hμy hax hay, ha x y, h.1, h.2]
    simp

end

end ManuscriptAudit.Paper10CoulombProductRule

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10CoulombProductRule.codifferential_eq_coordinateDivergence,
      ``ManuscriptAudit.Paper10CoulombProductRule.codifferential_scale,
      ``ManuscriptAudit.Paper10CoulombProductRule.preservesCoclosedAt_iff_partials_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
