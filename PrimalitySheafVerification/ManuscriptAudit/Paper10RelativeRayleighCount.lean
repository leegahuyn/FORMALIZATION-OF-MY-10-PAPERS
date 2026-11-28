import Lean.Util.CollectAxioms
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The two-sided eigenvalue counting comparison induced by the actual relative
quadratic-form inequalities on a common form domain. -/

namespace ManuscriptAudit.Paper10RelativeRayleighCount

open Module

variable {D : Type*} [AddCommGroup D] [Module ℝ D]

/-- A variational count records the largest dimension of a subspace whose
nonzero vectors have energy strictly below a fixed threshold. -/
def IsRayleighCount (Q M : D → ℝ) (R : ℝ) (N : ℕ) : Prop :=
  (∃ W : Submodule ℝ D, finrank ℝ W = N ∧
    ∀ u : W, u ≠ 0 → Q u < R * M u) ∧
  (∀ W : Submodule ℝ D, (∀ u : W, u ≠ 0 → Q u < R * M u) → finrank ℝ W ≤ N)

/-- Strict relative bounds compare the actual variational counts at the adjusted
upper and lower energy thresholds. -/
theorem count_comparison (Q V M : D → ℝ) (a b E : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1)
    (bound : ∀ u, |V u| ≤ a * Q u + b * M u)
    (nLow nPert nHigh : ℕ)
    (hLow : IsRayleighCount Q M ((E-b)/(1+a)) nLow)
    (hPert : IsRayleighCount (fun u => Q u + V u) M E nPert)
    (hHigh : IsRayleighCount Q M ((E+b)/(1-a)) nHigh) :
    nLow ≤ nPert ∧ nPert ≤ nHigh := by
  have hp : 0 < 1+a := add_pos_of_pos_of_nonneg zero_lt_one ha₀
  have hm : 0 < 1-a := sub_pos.mpr ha
  constructor
  · obtain ⟨W, hd, hW⟩ := hLow.1
    rw [← hd]
    apply hPert.2 W
    intro u hu
    have hV := (le_abs_self (V u)).trans (bound u)
    have hQ : (1+a) * Q u < (E-b) * M u := by
      calc
        _ < (1+a) * (((E-b)/(1+a)) * M u) := mul_lt_mul_of_pos_left (hW u hu) hp
        _ = _ := by field_simp [hp.ne'] <;> ring
    nlinarith only [hV, hQ]
  · obtain ⟨W, hd, hW⟩ := hPert.1
    rw [← hd]
    apply hHigh.2 W
    intro u hu
    have hV := (neg_le_abs (V u)).trans (bound u)
    have hP := hW u hu
    have hQ : (1-a) * Q u < (E+b) * M u := by nlinarith only [hV, hP]
    apply (mul_lt_mul_left₀ hm).mp
    calc
      _ < (E+b) * M u := hQ
      _ = _ := by field_simp [hm.ne'] <;> ring

end ManuscriptAudit.Paper10RelativeRayleighCount

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeRayleighCount.count_comparison
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
