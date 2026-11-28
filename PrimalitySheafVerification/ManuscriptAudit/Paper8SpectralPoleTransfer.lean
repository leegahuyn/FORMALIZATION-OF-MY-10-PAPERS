import Lean.Util.CollectAxioms
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt

/-! Pull a spectral pole back through the manuscript's exact relation λ=(1-w²)/4. -/

namespace ManuscriptAudit.Paper8SpectralPoleTransfer

open Filter Set
open scoped Topology

noncomputable section

def shiftedMaassEnergy (w : ℂ) : ℂ := (1 - w ^ 2) / 4

theorem shiftedMaassEnergy_analyticAt (w : ℂ) : AnalyticAt ℂ shiftedMaassEnergy w := by
  unfold shiftedMaassEnergy
  fun_prop

theorem shiftedMaassEnergy_deriv (w : ℂ) : deriv shiftedMaassEnergy w = -w / 2 := by
  have h : HasDerivAt shiftedMaassEnergy (-w / 2) w := by
    unfold shiftedMaassEnergy
    convert ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_pow 2 w)).div_const (4 : ℂ) using 1 <;>
      norm_num <;> ring
  exact h.deriv

private theorem shiftedMaassEnergy_order_at_zero :
    analyticOrderAt (fun w => shiftedMaassEnergy w - shiftedMaassEnergy 0) 0 = 2 := by
  have h : AnalyticAt ℂ (fun w => shiftedMaassEnergy w - shiftedMaassEnergy 0) 0 :=
    (shiftedMaassEnergy_analyticAt 0).sub analyticAt_const
  have hO : analyticOrderAt (fun w => shiftedMaassEnergy w - shiftedMaassEnergy 0) 0 = (2 : ℕ) := by
    refine (h.analyticOrderAt_eq_natCast).2
      ⟨fun _ => (-1 / 4 : ℂ), analyticAt_const, by norm_num, Eventually.of_forall (fun w => ?_)⟩
    unfold shiftedMaassEnergy
    rw [smul_eq_mul]
    ring
  exact_mod_cast hO

theorem shiftedMaassEnergy_comp_simple_spectral_pole {F : ℂ → ℂ} {w : ℂ}
    (hM : MeromorphicAt F (shiftedMaassEnergy w))
    (hO : meromorphicOrderAt F (shiftedMaassEnergy w) = (-1 : ℤ)) :
    MeromorphicAt (F ∘ shiftedMaassEnergy) w ∧
      meromorphicOrderAt (F ∘ shiftedMaassEnergy) w = (if w = 0 then (-2 : ℤ) else -1) := by
  classical
  have hA := shiftedMaassEnergy_analyticAt w
  refine ⟨hM.comp_analyticAt hA, ?_⟩
  by_cases hw : w = 0
  · subst w
    have hNC : ¬ EventuallyConst shiftedMaassEnergy (𝓝 (0 : ℂ)) := by
      rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, shiftedMaassEnergy_order_at_zero]
      simp
    rw [if_pos rfl, hM.meromorphicOrderAt_comp (shiftedMaassEnergy_analyticAt 0) hNC, hO,
      shiftedMaassEnergy_order_at_zero]
    norm_num [ENat.map_coe]
  · have hD : deriv shiftedMaassEnergy w ≠ 0 := by
      rw [shiftedMaassEnergy_deriv]
      exact div_ne_zero (neg_ne_zero.mpr hw) (by norm_num)
    rwa [if_neg hw, meromorphicOrderAt_comp_of_deriv_ne_zero hA hD]

theorem spectral_pole_preserved_by_analytic_factor_and_remainder {F A B : ℂ → ℂ} {w : ℂ}
    (hF : MeromorphicAt F w) (hPole : meromorphicOrderAt F w < 0)
    (hA : AnalyticAt ℂ A w) (hA₀ : A w ≠ 0) (hB : AnalyticAt ℂ B w) :
    MeromorphicAt (A * F + B) w ∧ meromorphicOrderAt (A * F + B) w = meromorphicOrderAt F w := by
  refine ⟨(hA.meromorphicAt.mul hF).add hB.meromorphicAt, ?_⟩
  have hEq : meromorphicOrderAt (A * F) w = meromorphicOrderAt F w :=
    meromorphicOrderAt_mul_of_ne_zero hA hA₀
  rw [meromorphicOrderAt_add_eq_left_of_lt hB.meromorphicAt, hEq]
  rw [hEq]
  exact hPole.trans_le hB.meromorphicOrderAt_nonneg

theorem exists_shiftedMaassEnergy_of_real_above_eta_threshold {λ : ℝ} (hλ : (3 / 16 : ℝ) < λ) :
    ∃ w : ℂ, shiftedMaassEnergy w = (λ : ℂ) ∧ 0 ≤ w.re ∧ w.re < 1 / 2 := by
  by_cases h : λ ≤ 1 / 4
  · have hArg : 0 ≤ 1 - 4 * λ := by linarith
    let r := Real.sqrt (1 - 4 * λ)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hSq : r ^ 2 = 1 - 4 * λ := Real.sq_sqrt hArg
    refine ⟨(r : ℂ), ?_, ?_, ?_⟩
    · unfold shiftedMaassEnergy
      rw [← Complex.ofReal_pow, hSq]
      push_cast <;> ring
    · rwa [Complex.ofReal_re]
    · rw [Complex.ofReal_re]
      have hS : r ^ 2 < (1 / 2 : ℝ) ^ 2 := by rw [hSq]; linarith
      simpa only [abs_of_nonneg hr, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using sq_lt_sq.mp hS
  · have hArg : 0 ≤ 4 * λ - 1 := by linarith [lt_of_not_ge h]
    let r := Real.sqrt (4 * λ - 1)
    have hSq : r ^ 2 = 4 * λ - 1 := Real.sq_sqrt hArg
    refine ⟨(r : ℂ) * Complex.I, ?_, ?_, ?_⟩
    · unfold shiftedMaassEnergy
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hSq]
      push_cast
      ring
    · norm_num [Complex.mul_re]
    · norm_num [Complex.mul_re]

end
end ManuscriptAudit.Paper8SpectralPoleTransfer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SpectralPoleTransfer.shiftedMaassEnergy_comp_simple_spectral_pole,
      ``ManuscriptAudit.Paper8SpectralPoleTransfer.spectral_pole_preserved_by_analytic_factor_and_remainder,
      ``ManuscriptAudit.Paper8SpectralPoleTransfer.exists_shiftedMaassEnergy_of_real_above_eta_threshold] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
