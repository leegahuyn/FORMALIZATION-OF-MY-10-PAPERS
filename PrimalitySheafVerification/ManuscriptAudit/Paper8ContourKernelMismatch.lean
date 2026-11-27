import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8LocalContour

/-!
# The two p. 335 contour kernels differ on their common admissible circle

The printed coefficients (2/3,16) and the primary coefficients (23,24)
from Rhoades, https://arxiv.org/pdf/1111.1495, give strictly different
integrand values. This comparison is at an actual nonzero contour point
and uses the same positive Laurent series in both integrands.
-/

namespace ManuscriptAudit.Paper8ContourKernelMismatch

open Paper8ContourGammaSeries (a term majorant coefficient_pos majorant_summable)
open Paper8LocalContour (denominator factor integrand radius)
open Paper8HolomorphicPartPhase (qParameter periodCoefficient)

noncomputable section

theorem a_at_positive_real {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 < A ∧ a k (r : ℂ) = (A : ℂ) := by
  have hSum := majorant_summable hk hr
  have hPos (m : ℕ) : 0 < majorant k r m :=
    div_pos (coefficient_pos hk m) (pow_pos hr _)
  have h0 := hSum.sum_le_tsum ({0} : Finset ℕ) (fun m _ => (hPos m).le)
  have h0' : majorant k r 0 ≤ ∑' m : ℕ, majorant k r m := by
    simpa only [Finset.sum_singleton] using h0
  refine ⟨∑' m : ℕ, majorant k r m, (hPos 0).trans_le h0', ?_⟩
  have h := Complex.ofRealCLM.hasSum hSum.hasSum
  change HasSum (fun m : ℕ => (majorant k r m : ℂ))
    ((∑' m : ℕ, majorant k r m : ℝ) : ℂ) at h
  have hTerm (m : ℕ) : term k m (r : ℂ) = (majorant k r m : ℂ) := by
    simp only [term, majorant, Complex.ofReal_div, Complex.ofReal_pow]
  exact (h.congr_fun hTerm).tsum_eq

private theorem q_at_I : qParameter Complex.I = (Real.exp (-(2 * Real.pi)) : ℂ) := by
  rw [qParameter, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [periodCoefficient]
  calc
    _ = (2 : ℂ) * (Real.pi : ℂ) * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem integrand_at_positive_real (k : ℕ) (α β r A : ℝ)
    (hA : a k (r : ℂ) = (A : ℂ)) :
    integrand α β k 0 Complex.I (r : ℂ) =
      ((A * Real.exp (α * r) / (1 - Real.exp (-(2 * Real.pi) + β * r)) : ℝ) : ℂ) := by
  have hExp (c : ℝ) : Complex.exp ((c : ℂ) * (r : ℂ)) = (Real.exp (c * r) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [integrand, hA, denominator, factor, zpow_zero, one_mul, q_at_I, hExp α, hExp β]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Real.exp_add]

theorem integrands_strict_on_positive_real {k : ℕ} (hk : 0 < k) {r : ℝ}
    (hr : 0 < r) (hr' : r < Real.pi / 12) :
    (integrand (2 / 3) 16 k 0 Complex.I (r : ℂ)).re <
      (integrand 23 24 k 0 Complex.I (r : ℂ)).re := by
  obtain ⟨A, hApos, hA⟩ := a_at_positive_real hk hr
  rw [integrand_at_positive_real k (2 / 3) 16 r A hA,
    integrand_at_positive_real k 23 24 r A hA,
    Complex.ofReal_re, Complex.ofReal_re]
  have hDen : 0 < 1 - Real.exp (-(2 * Real.pi) + 24 * r) := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hOrder : 1 - Real.exp (-(2 * Real.pi) + 24 * r) ≤
      1 - Real.exp (-(2 * Real.pi) + 16 * r) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
  have hNum : A * Real.exp ((2 / 3) * r) < A * Real.exp (23 * r) :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hApos
  calc
    _ ≤ A * Real.exp ((2 / 3) * r) / (1 - Real.exp (-(2 * Real.pi) + 24 * r)) :=
      div_le_div_of_nonneg_left (mul_pos hApos (Real.exp_pos _)).le hDen hOrder
    _ < _ := div_lt_div_of_pos_right hNum hDen

def samplePoint : ℂ := ((Real.pi / 24 : ℝ) : ℂ)

theorem samplePoint_mem_circle :
    samplePoint ∈ Metric.sphere (0 : ℂ) (radius Complex.I) := by
  have hr : 0 ≤ Real.pi / 24 := (div_pos Real.pi_pos (by norm_num)).le
  simp only [samplePoint, radius, Metric.mem_sphere, dist_zero_right, Complex.I_im, abs_one,
    mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

theorem integrands_ne_at_shared_circle {k : ℕ} (hk : 0 < k) :
    integrand (2 / 3) 16 k 0 Complex.I samplePoint ≠
      integrand 23 24 k 0 Complex.I samplePoint := by
  have hr : 0 < Real.pi / 24 := div_pos Real.pi_pos (by norm_num)
  have hr' : Real.pi / 24 < Real.pi / 12 := by linarith [Real.pi_pos]
  intro h
  exact (ne_of_lt (integrands_strict_on_positive_real hk hr hr')) (congrArg Complex.re h)

end
end ManuscriptAudit.Paper8ContourKernelMismatch

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourKernelMismatch.a_at_positive_real,
      ``ManuscriptAudit.Paper8ContourKernelMismatch.integrands_strict_on_positive_real,
      ``ManuscriptAudit.Paper8ContourKernelMismatch.samplePoint_mem_circle,
      ``ManuscriptAudit.Paper8ContourKernelMismatch.integrands_ne_at_shared_circle] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
