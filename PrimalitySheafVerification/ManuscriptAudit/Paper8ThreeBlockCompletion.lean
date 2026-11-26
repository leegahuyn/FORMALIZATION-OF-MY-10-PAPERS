import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.AppellHalfBlocks
import PrimalitySheafVerification.ManuscriptAudit.ZwegersHalfPeriod

/-!
# The literal completed three-block model of Paper 8

For the three displayed blocks and any three coefficients, the
holomorphic block combination and the half-period correction vanish
on the upper half-plane. The stated nonzero-shadow law fails for the
printed coefficients whose sum is one.
-/

namespace ManuscriptAudit.Paper8ThreeBlockCompletion

open AppellSameIntegerShift AppellHalfBlocks Paper8XiShadow ZwegersHalfPeriod
open MaassLaplacian (partialX partialY)
open Filter Topology

noncomputable section

def completed (a b c α τ : ℂ) : ℂ :=
  a * mu (τ / 2) (τ / 2 + 1 / 2) τ +
  b * mu (τ / 2 + τ) (τ / 2 + 1 / 2 + τ) τ +
  c * mu (τ / 2 + 1 / 2) (τ / 2 + 1) τ +
  α * (a + b + c) * correction τ

theorem completed_eq_zero (a b c α τ : ℂ) (hτ : 0 < τ.im) :
    completed a b c α τ = 0 := by
  obtain ⟨ha, hb, hc⟩ := paper8_displayed_three_blocks_zero τ hτ
  simp only [completed, ha, hb, hc, correction_eq_zero, mul_zero, add_zero]

private def upperParameter (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

private theorem upperParameter_im (x y : ℝ) : (upperParameter x y).im = y := by
  simp [upperParameter, Complex.add_im, Complex.mul_im]

private def field (a b c α : ℂ) : Paper8XiShadow.Field :=
  fun x y => completed a b c α (upperParameter x y)

theorem completed_xi_zero (a b c α : ℂ) (x y : ℝ) (hy : 0 < y) :
    xiHalf (field a b c α) x y = 0 := by
  have hzero (u v : ℝ) (hv : 0 < v) : field a b c α u v = 0 :=
    completed_eq_zero _ _ _ _ _ (by rwa [upperParameter_im])
  have hx : partialX (field a b c α) x y = 0 := by
    unfold partialX
    rw [show (fun t => field a b c α t y) = (fun _ => (0 : ℂ)) by
      funext t
      exact hzero t y hy]
    exact deriv_const x 0
  have hy' : partialY (field a b c α) x y = 0 := by
    have hEv : (fun t => field a b c α x t) =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) :=
      (eventually_gt_nhds hy).mono (fun t ht => hzero x t ht)
    unfold partialY
    rw [hEv.deriv_eq]
    exact deriv_const y 0
  simp [xiHalf, dBar, hx, hy']

/-- The three coefficients printed in ND2 cannot have the prescribed nonzero shadow. -/
theorem printed_three_block_shadow_refuted (α : ℂ) :
    ¬ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x y : ℝ, 0 < y →
      xiHalf (field 1 (-1 / 2) (1 / 2) α) x y = κ * printedTheta (upperParameter x y) := by
  rintro ⟨κ, hκ, h⟩
  have hI : upperParameter 0 1 = Complex.I := by simp [upperParameter]
  have hZero := h 0 1 zero_lt_one
  rw [completed_xi_zero _ _ _ _ _ _ zero_lt_one, hI] at hZero
  exact (mul_ne_zero hκ printedTheta_at_I_ne_zero) hZero.symm

end

end ManuscriptAudit.Paper8ThreeBlockCompletion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ThreeBlockCompletion.completed_eq_zero,
      ``ManuscriptAudit.Paper8ThreeBlockCompletion.completed_xi_zero,
      ``ManuscriptAudit.Paper8ThreeBlockCompletion.printed_three_block_shadow_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
