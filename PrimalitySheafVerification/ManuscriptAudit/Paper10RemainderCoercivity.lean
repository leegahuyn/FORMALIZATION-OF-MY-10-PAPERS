import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Local bounded-set control of a remainder does not imply the lower bound in Remark 3.7. -/

namespace ManuscriptAudit.Paper10RemainderCoercivity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def leading (a : ℝ) (v : V) : ℝ := a * ‖v‖^2

def mass (v : V) : ℝ := ‖v‖^2

def remainder (v : V) : ℝ := -(‖v‖^4)

def action (a : ℝ) (v : V) : ℝ := leading a v + mass v + 0 + remainder v

theorem remainder_controlled_on_bounded_sets (v : V) {R : ℝ} (hR : ‖v‖ ≤ R) :
    |remainder v| ≤ R^4 := by
  rw [remainder, abs_neg, abs_of_nonneg (by positivity)]
  gcongr

theorem positive_mass_and_absorbable_zero_penalty (v : V) {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    mass v ≥ 1 * ‖v‖^2 - 0 ∧ |(0 : ℝ)| ≤ δ * leading a v + 0 := by
  constructor
  · simp [mass]
  · simp only [abs_zero, add_zero]
    exact mul_nonneg hδ (mul_nonneg ha (sq_nonneg _))

theorem action_unbounded_on_every_nonzero_ray (a : ℝ) {v : V} (hv : v ≠ 0) (B : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ action a (t • v) < B := by
  let C := |a+1| + |B| + 2
  have hC : 2 ≤ C := by dsimp only [C]; linarith [abs_nonneg (a+1), abs_nonneg B]
  have hC0 : 0 ≤ C := by linarith
  have hC1 : 0 ≤ C-1 := by linarith
  have hC2 : C ≤ C^2 := by nlinarith [mul_nonneg hC0 hC1]
  have hCα : a+1 - C^2 ≤ -1 := by
    have h₁ : a+1 ≤ |a+1| := le_abs_self _
    have h₂ : |a+1| + 2 ≤ C := by dsimp only [C]; linarith [abs_nonneg B]
    linarith
  have hCB : -(C^2) < B := by
    have h₁ : -B ≤ |B| := neg_le_abs _
    have h₂ : |B| + 2 ≤ C := by dsimp only [C]; linarith [abs_nonneg (a+1)]
    linarith
  let t := C / ‖v‖
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 ≤ t := div_nonneg (by linarith) hv₀.le
  have hNorm : ‖t • v‖ = C := by
    rw [norm_smul, Real.norm_of_nonneg ht]
    exact div_mul_cancel₀ C hv₀.ne'
  refine ⟨t, ht, ?_⟩
  calc
    action a (t • v) = (a+1-C^2)*C^2 := by
      unfold action leading mass remainder
      rw [hNorm]
      ring
    _ ≤ -(C^2) := by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hCα (sq_nonneg C)
    _ < B := hCB

/-- Global estimates on both lower-order blocks give a uniform lower bound. -/
theorem global_absorption_lower_bound (curvature normSq lead m v r : ℝ)
    (cF cM epsV epsR epsM C0 CV CR : ℝ)
    (hLead : cF * curvature ≤ lead) (hMass : cM * normSq - C0 ≤ m)
    (hV : |v| ≤ epsV * curvature + CV)
    (hR : |r| ≤ epsR * curvature + epsM * normSq + CR) :
    (cF - epsV - epsR)*curvature + (cM - epsM)*normSq - (C0+CV+CR) ≤
      lead + m + v + r := by
  nlinarith only [hLead, hMass, hV, hR, neg_abs_le v, neg_abs_le r]

end ManuscriptAudit.Paper10RemainderCoercivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10RemainderCoercivity.remainder_controlled_on_bounded_sets,
      ``ManuscriptAudit.Paper10RemainderCoercivity.positive_mass_and_absorbable_zero_penalty,
      ``ManuscriptAudit.Paper10RemainderCoercivity.action_unbounded_on_every_nonzero_ray,
      ``ManuscriptAudit.Paper10RemainderCoercivity.global_absorption_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
