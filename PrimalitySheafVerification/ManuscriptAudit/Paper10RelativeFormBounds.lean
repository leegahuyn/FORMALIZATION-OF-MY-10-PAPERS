import Lean.Util.CollectAxioms
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative form bounds for the relative perturbation in Paper 10, (4.48). -/

namespace ManuscriptAudit.Paper10RelativeFormBounds

variable {D : Type*}

/-- The perturbed form has the lower bound prescribed by the relative form estimate. -/
theorem semibounded (q v N : D → ℝ) (m a b : ℝ) (ha : a < 1)
    (hq : ∀ x, -m * N x ≤ q x) (hv : ∀ x, |v x| ≤ a * q x + b * N x) (x : D) :
    -((1 - a) * m + b) * N x ≤ q x + v x := by
  have h₁ := (abs_le.mp (hv x)).1
  have h₂ := mul_le_mul_of_nonneg_left (hq x) (sub_nonneg.mpr ha.le)
  calc
    _ = (1 - a) * (-m * N x) - b * N x := by ring
    _ ≤ (1 - a) * q x - b * N x := sub_le_sub_right h₂ _
    _ ≤ _ := by linarith

/-- A positive shift gives two-sided comparison of the actual perturbed and original diagonals. -/
theorem shifted_comparison (q v N : D → ℝ) (m a b : ℝ)
    (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (hb : 0 ≤ b)
    (hN : ∀ x, 0 ≤ N x) (hq : ∀ x, -m * N x ≤ q x)
    (hv : ∀ x, |v x| ≤ a * q x + b * N x) (x : D) :
    (1 - a) * (q x + (m + 1) * N x) ≤
        q x + v x + ((1 - a) * (m + 1) + b) * N x ∧
      q x + v x + ((1 - a) * (m + 1) + b) * N x ≤
        (1 + a + 2 * b) * (q x + (m + 1) * N x) := by
  let Q := q x + (m + 1) * N x
  have hQ : N x ≤ Q := by
    dsimp [Q]
    nlinarith only [hq x]
  have hShift : 0 ≤ 2 * a * (m + 1) * N x :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha₀)
      (add_nonneg hm zero_le_one)) (hN x)
  have hUpper := mul_le_mul_of_nonneg_left hQ (mul_nonneg (by norm_num) hb : 0 ≤ 2*b)
  have h₁ := (abs_le.mp (hv x)).1
  have h₂ := (abs_le.mp (hv x)).2
  constructor
  · nlinarith only [h₁]
  · calc
      _ ≤ (1 + a) * Q + 2*b*N x := by dsimp [Q]; nlinarith only [h₂, hShift]
      _ ≤ (1 + a) * Q + 2*b*Q := by nlinarith only [hUpper]
      _ = _ := by dsimp [Q]; ring

end ManuscriptAudit.Paper10RelativeFormBounds

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10RelativeFormBounds.semibounded,
      ``ManuscriptAudit.Paper10RelativeFormBounds.shifted_comparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
