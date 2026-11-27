import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-! The two literal positive-index definitions of ψ in Paper 8 give different series. -/

namespace ManuscriptAudit.Paper8PartialThetaDefinitions

open Paper8ExteriorProductCorrection

noncomputable section

/-- Equation (G.6), with the printed positive index written as n+1. -/
def triangularTerm (q : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * q ^ ((n + 1) * (n + 2) / 2)

def triangularTheta (q : ℝ) : ℝ := ∑' n : ℕ, triangularTerm q n

theorem triangularTerm_eq_neg_correction (q : ℝ) (n : ℕ) :
    triangularTerm q n = -correctionNumeratorTerm q (n + 1) := by
  rw [triangularTerm, correctionNumeratorTerm, pow_succ]
  change (-1 : ℝ) ^ n * q ^ ((n + 1) * (n + 2) / 2) =
    -(((-1 : ℝ) ^ n * -1) * q ^ ((n + 1) * (n + 2) / 2))
  ring

private theorem triangular_exponent_ge (n : ℕ) : n + 1 ≤ (n + 1) * (n + 2) / 2 := by
  have h := Nat.mul_le_mul_left (n + 1) (show 2 ≤ n + 2 by omega)
  rw [Nat.mul_comm (n + 1) 2] at h
  omega

private theorem triangularTerm_abs_le {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    |triangularTerm q n| ≤ q ^ (n + 1) := by
  rw [triangularTerm, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hq _)]
  exact pow_le_pow_of_le_one hq h₁ (triangular_exponent_ge n)

theorem triangularTheta_abs_le {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    |triangularTheta q| ≤ q / (1 - q) := by
  have hGeom : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq.le h₁).mul_left q
  unfold triangularTheta
  simpa only [Real.norm_eq_abs] using
    (tsum_of_norm_bounded hGeom (f := triangularTerm q)
      (fun n => by rw [Real.norm_eq_abs]; exact triangularTerm_abs_le hq.le h₁.le n))

/-- At q=2⁻²⁴ the positive-index Kronecker series exceeds the triangular series
by at least one half. -/
theorem printed_partial_theta_gap_at_testQ :
    (1 : ℝ) / 2 ≤ unilateralTheta testQ - triangularTheta testQ := by
  have hq : 0 < testQ := by norm_num [testQ]
  have h₁ : testQ < 1 := by norm_num [testQ]
  have hq₄ : testQ ≤ 1 / 4 := by norm_num [testQ]
  have hS : triangularTheta testQ ≤ 1 / 3 := by
    apply (le_abs_self _).trans ((triangularTheta_abs_le hq h₁).trans ?_)
    exact (div_le_iff₀ (sub_pos.mpr h₁)).mpr (by linarith)
  linarith [unilateralTheta_testQ_ge]

theorem printed_partial_theta_definitions_differ :
    unilateralTheta testQ ≠ triangularTheta testQ := by
  intro h
  have hb := printed_partial_theta_gap_at_testQ
  rw [h, sub_self] at hb
  norm_num at hb

end
end ManuscriptAudit.Paper8PartialThetaDefinitions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PartialThetaDefinitions.triangularTerm_eq_neg_correction,
      ``ManuscriptAudit.Paper8PartialThetaDefinitions.triangularTheta_abs_le,
      ``ManuscriptAudit.Paper8PartialThetaDefinitions.printed_partial_theta_gap_at_testQ,
      ``ManuscriptAudit.Paper8PartialThetaDefinitions.printed_partial_theta_definitions_differ] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
