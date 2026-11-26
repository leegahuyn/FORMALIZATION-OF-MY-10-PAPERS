import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfilesNonzero
import PrimalitySheafVerification.ManuscriptAudit.ThetaQSeriesAnalytic

/-! The three native level-two theta profiles extend over their cusps. -/

namespace ManuscriptAudit.ThetaCuspPolarData

open Set
open Paper9ThetaCuspPhases ThetaProfilesNonzero ThetaQSeriesAnalytic
open scoped UpperHalfPlane

noncomputable section

def quarterParameter (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4)

private theorem quarterParameter_fourth (τ : ℂ) : quarterParameter τ ^ 4 = cuspQ τ := by
  rw [quarterParameter, cuspQ, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

private def halfTerm (n : ℕ) (q : ℂ) : ℂ := q ^ (4 * n * (n + 1))

private theorem halfTerm_differentiable (n : ℕ) : Differentiable ℂ (halfTerm n) := by
  unfold halfTerm
  fun_prop

private def halfSum (q : ℂ) : ℂ := ∑' n : ℕ, halfTerm n q

private theorem halfSum_differentiableAt {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ halfSum q := by
  let r := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hR : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hD : DifferentiableOn ℂ halfSum (Metric.ball (0 : ℂ) r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := halfTerm)
      (summable_geometric_of_lt_one hr hR)
      (fun n => (halfTerm_differentiable n).differentiableOn) Metric.isOpen_ball ?_
    intro n w hw
    have hw' : ‖w‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hn : n ≤ 4 * n * (n + 1) := by
      calc
        n ≤ 4 * n := by omega
        _ ≤ 4 * n * (n + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
    exact norm_power_le_radius hn hR.le hw'.le
  exact (hD q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)

def halfProfileQ (q : ℂ) : ℂ := q * (2 * halfSum q)

def profileQ (i : Fin 3) (q : ℂ) : ℂ :=
  if i = 2 then halfProfileQ q else thetaQ (q ^ 4)

theorem profileQ_differentiableOn_unit_disk (i : Fin 3) :
    DifferentiableOn ℂ (profileQ i) (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hNorm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  by_cases hi : i = 2
  · have he : profileQ i = halfProfileQ := by
      funext w
      simp [profileQ, hi]
    rw [he]
    change DifferentiableWithinAt ℂ (fun w => w * (2 * halfSum w)) (Metric.ball 0 1) q
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (2 : ℂ)) q := differentiableAt_const _
    have hId : DifferentiableAt ℂ (fun w : ℂ => w) q := by fun_prop
    exact (hId.mul (hc.mul (halfSum_differentiableAt hNorm))).differentiableWithinAt
  · have he : profileQ i = fun w => thetaQ (w ^ (4 : ℕ)) := by
      funext w
      simp [profileQ, hi]
    rw [he]
    have hq4 : q ^ (4 : ℕ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hNorm (by decide)
    have h₀ := (thetaQ_differentiableOn_unit_disk _ hq4).differentiableAt
      (Metric.isOpen_ball.mem_nhds hq4)
    have h₁ : DifferentiableAt ℂ (fun w : ℂ => w ^ (4 : ℕ)) q := by fun_prop
    exact (h₀.comp q h₁).differentiableWithinAt

theorem normalizedProfile_eq (i : Fin 3) (z : ℍ) :
    normalizedProfile i z = profileQ i (quarterParameter z) := by
  fin_cases i
  · change normalizedProfile 0 z = profileQ 0 (quarterParameter z)
    rw [normalizedProfile_zero, jacobiTheta_eq_thetaQ z.im_pos]
    simp only [profileQ, if_neg (by decide : (0 : Fin 3) ≠ 2), quarterParameter_fourth]
  · change normalizedProfile 1 z = profileQ 1 (quarterParameter z)
    rw [normalizedProfile_one, jacobiTheta_eq_thetaQ z.im_pos]
    simp only [profileQ, if_neg (by decide : (1 : Fin 3) ≠ 2), quarterParameter_fourth]
  · change normalizedProfile 2 z = profileQ 2 (quarterParameter z)
    rw [normalizedProfile_two, thetaHalfShift_eq_quarter_series z.im_pos]
    simp only [profileQ, if_pos rfl, halfProfileQ, halfSum, halfTerm, quarterParameter]

theorem profileQ_at_zero (i : Fin 3) :
    profileQ i 0 = if i = 2 then 0 else 1 := by
  by_cases hi : i = 2 <;> simp [profileQ, halfProfileQ, hi, thetaQ_zero]

/-- Cauchy's formula for the coefficient of q^(-n-1). -/
def negativeCoefficient (f : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  ((2 : ℂ) * Real.pi * Complex.I)⁻¹ * circleIntegral (fun q => f q * q ^ n) 0 R

theorem negativeCoefficient_eq_zero_of_holomorphic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) {R : ℝ} (hR : R ∈ Ioo 0 1)
    (n : ℕ) : negativeCoefficient f R n = 0 := by
  have hPower : DifferentiableOn ℂ (fun q : ℂ => q ^ n) (Metric.ball (0 : ℂ) 1) := by
    fun_prop
  have hD : DifferentiableOn ℂ (fun q => f q * q ^ n) (Metric.ball (0 : ℂ) 1) :=
    hf.mul hPower
  have hSub : closure (Metric.ball (0 : ℂ) R) ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hR.2)
  have hi := (hD.mono hSub).diffContOnCl.circleIntegral_eq_zero hR.1.le
  rw [negativeCoefficient, hi, mul_zero]

theorem profileQ_negativeCoefficients_zero (i : Fin 3) {R : ℝ} (hR : R ∈ Ioo 0 1)
    (n : ℕ) : negativeCoefficient (profileQ i) R n = 0 :=
  negativeCoefficient_eq_zero_of_holomorphic (profileQ_differentiableOn_unit_disk i) hR n

theorem nonzero_profiles_with_zero_polar_data :
    (∀ i : Fin 3, ∀ R ∈ Ioo (0 : ℝ) 1, ∀ n,
      negativeCoefficient (profileQ i) R n =
        negativeCoefficient (fun _ => 0) R n) ∧
    profileQ 0 ≠ (fun _ => 0) := by
  constructor
  · intro i R hR n
    rw [profileQ_negativeCoefficients_zero i hR n,
      negativeCoefficient_eq_zero_of_holomorphic (by fun_prop) hR n]
  · intro h
    have hz : profileQ 0 0 = 0 := congrFun h 0
    rw [profileQ_at_zero, if_neg (by decide : (0 : Fin 3) ≠ 2)] at hz
    exact one_ne_zero hz

end
end ManuscriptAudit.ThetaCuspPolarData

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaCuspPolarData.profileQ_differentiableOn_unit_disk,
      ``ManuscriptAudit.ThetaCuspPolarData.normalizedProfile_eq,
      ``ManuscriptAudit.ThetaCuspPolarData.profileQ_at_zero,
      ``ManuscriptAudit.ThetaCuspPolarData.negativeCoefficient_eq_zero_of_holomorphic,
      ``ManuscriptAudit.ThetaCuspPolarData.profileQ_negativeCoefficients_zero,
      ``ManuscriptAudit.ThetaCuspPolarData.nonzero_profiles_with_zero_polar_data] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
