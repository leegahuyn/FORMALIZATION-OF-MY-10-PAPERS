import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OddTheta

/-! The actual principal character modulo four does not give the printed strip bound. -/

namespace ManuscriptAudit.Paper9PrincipalThetaStrip

open Complex

noncomputable section

/-- The principal character modulo four, evaluated on actual integer arguments. -/
def principalChar (n : ℤ) : ℂ := if n % 2 = 1 then 1 else 0

def principalTheta (τ : ℂ) : ℂ :=
  ∑' n : ℤ, principalChar n * jacobiTheta₂_term n 0 τ

private theorem principalTheta_summable (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => principalChar n * jacobiTheta₂_term n 0 τ) := by
  have hg : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 τ‖) :=
    (summable_norm_iff (E := ℂ)).2 ((summable_jacobiTheta₂_term_iff 0 τ).2 hτ)
  apply hg.of_norm_bounded
  intro n
  by_cases hn : n % 2 = 1 <;> simp [principalChar, hn]

private def realTerm (y : ℝ) (n : ℤ) : ℝ :=
  if n % 2 = 1 then Real.exp (-Real.pi * (y * (n : ℝ) ^ 2)) else 0

private theorem realTerm_axis (y : ℝ) (n : ℤ) :
    (principalChar n * jacobiTheta₂_term n 0 ((y : ℂ) * Complex.I)).re = realTerm y n := by
  by_cases hn : n % 2 = 1
  · simp only [principalChar, realTerm, if_pos hn, one_mul, jacobiTheta₂_term,
      mul_zero, zero_add]
    have he : (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * ((y : ℂ) * Complex.I) =
        ((-Real.pi * (y * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
      push_cast
      calc
        _ = ((Real.pi : ℂ) * (y : ℂ) * (n : ℂ) ^ 2) * (Complex.I * Complex.I) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [he, Complex.exp_ofReal_re]
  · simp [principalChar, realTerm, hn]

theorem principalTheta_re_axis_lower (y : ℝ) (hy : 0 < y) :
    Real.exp (-Real.pi * y) ≤ (principalTheta ((y : ℂ) * Complex.I)).re := by
  have hsum := principalTheta_summable ((y : ℂ) * Complex.I) (by simpa using hy)
  have hreal : HasSum (realTerm y) (principalTheta ((y : ℂ) * Complex.I)).re := by
    have h := Complex.reCLM.hasSum hsum.hasSum
    simpa only [Function.comp_def, Complex.reCLM_apply, realTerm_axis] using h
  have hle := Summable.le_tsum (i := (1 : ℤ)) (f := realTerm y)
    (fun n _ => by unfold realTerm; split <;> positivity) hreal.summable
  rw [hreal.tsum_eq] at hle
  simpa [realTerm] using hle

theorem principalTheta_norm_lower (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    Real.exp (-Real.pi) ≤ ‖principalTheta ((y : ℂ) * Complex.I)‖ := by
  calc
    _ ≤ Real.exp (-Real.pi * y) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    _ ≤ _ := principalTheta_re_axis_lower y hy
    _ ≤ _ := Complex.re_le_norm _

/-- The pointwise bound by C√y fails arbitrarily close to zero on the imaginary axis. -/
theorem no_sqrt_strip_bound (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ y : ℝ, 0 < y ∧ y < ε ∧
      C * Real.sqrt y < ‖principalTheta ((y : ℂ) * Complex.I)‖ := by
  let c := Real.exp (-Real.pi)
  let t := c / (2 * (C + 1))
  have hc : 0 < c := Real.exp_pos _
  have ht : 0 < t := div_pos hc (by linarith)
  let y := min (ε / 2) (min 1 (t ^ 2))
  have hy : 0 < y := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  have hyε : y < ε := (min_le_left _ _).trans_lt (by linarith)
  have hy1 : y ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hyt : y ≤ t ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hs : Real.sqrt y ≤ t := by
    rw [← Real.sqrt_sq ht.le]
    exact Real.sqrt_le_sqrt hyt
  have hct : C * t < c := by
    rw [show C * t = (C * c) / (2 * (C + 1)) by rw [mul_div_assoc]]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * (C + 1))).mpr
    nlinarith [mul_nonneg hC hc.le]
  exact ⟨y, hy, hyε, (mul_le_mul_of_nonneg_left hs hC).trans_lt
    (hct.trans_le (principalTheta_norm_lower y hy hy1))⟩

end
end ManuscriptAudit.Paper9PrincipalThetaStrip

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9PrincipalThetaStrip.principalTheta_re_axis_lower,
      ``ManuscriptAudit.Paper9PrincipalThetaStrip.principalTheta_norm_lower,
      ``ManuscriptAudit.Paper9PrincipalThetaStrip.no_sqrt_strip_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
