import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProgressionProfileFromEta
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenMainTermEvaluation

/-! The signed even zero mode has a strictly negative logarithmic main term under the explicit eta cutoff inputs. -/

namespace ManuscriptAudit.Paper8EvenZeroModeFromEta

open Filter
open scoped Topology
open Paper8EtaLevelZeroMode (etaPhase)
open Paper8ProgressionProfileFromEta
open Paper8EvenMainTermEvaluation (candidate_profile_combination_pos)
open Paper8ProgressionSqrtMainTerm (zeroModeProgressionRaw even_zero_mode_log_limit_of_sqrt_main_terms)
open Paper8EvenDenominatorWeightLimits (evenWeightLimit)
open Paper8EvenGcdOrderedLimit (evenSectorCutoff evenWeight)
open Paper8EvenCutoffLogLimit (even_sector_no_ordered_limit_of_log_limit)
open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8CutoffLog (cutoffLog)
open Paper8UnshiftedZeroMode (squareRootScale)

noncomputable section

theorem even_zero_mode_negative_log_limit (C : ℝ) (hC : 0 < C)
    (hAggregate : Tendsto normalizedAggregate atTop (𝓝 (C : ℂ)))
    (hLevelTwo : Tendsto (normalizedLevel 2) atTop (𝓝 (etaPhase * ((C : ℂ) / 3))))
    (hLevelFour : Tendsto (normalizedLevel 4) atTop (𝓝 (etaPhase * ((C : ℂ) / 6))))
    (hCross : Tendsto normalizedCross atTop (𝓝 0)) :
    ∃ L : ℂ, L.re < 0 ∧ Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N 0) atTop (𝓝 L) := by
  let A : ℕ → ℂ := fun r => if r = 0 ∨ r = 2 then (C : ℂ) / 6 else (C : ℂ) / 3
  obtain ⟨h0, h1, h2, h3⟩ := actual_progression_limits_of_level_and_cross
    C hAggregate hLevelTwo hLevelFour hCross
  have hInput : ∀ r ∈ Finset.range 4, Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j) atTop (𝓝 (A r)) := by
    intro r hr
    have hr4 := Finset.mem_range.mp hr
    change Tendsto (normalizedProgression r) atTop (𝓝 (A r))
    interval_cases r
    · simpa [A] using h0
    · simpa [A] using h1
    · simpa [A] using h2
    · simpa [A] using h3
  let M : ℂ := ∑ r ∈ Finset.range 4, evenWeightLimit r * A r
  let L : ℂ := (-(coefficient 1 0 / 2) : ℝ) • M
  have hM : 0 < M.re := candidate_profile_combination_pos C hC A
    (by simp [A]) (by simp [A]) (by simp [A]) (by simp [A])
  have hW : (-(coefficient 1 0 / 2) : ℝ) < 0 := by
    have hP := coefficient_pos (k := 1) (by decide) 0
    linarith
  have hL : L.re < 0 := by
    unfold L
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_neg_of_neg_of_pos hW hM
  have hSum : (∑ r ∈ Finset.range 4, (∑' h : ℕ, evenWeight (h + 1) r) *
      ((1 / 2 : ℝ) • (-(coefficient 1 0 : ℂ) * A r))) = L := by
    unfold L M
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    unfold evenWeightLimit
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  have hLimit := even_zero_mode_log_limit_of_sqrt_main_terms A hInput
  rw [hSum] at hLimit
  exact ⟨L, hL, hLimit⟩

theorem even_zero_mode_no_ordered_limit (C : ℝ) (hC : 0 < C)
    (hAggregate : Tendsto normalizedAggregate atTop (𝓝 (C : ℂ)))
    (hLevelTwo : Tendsto (normalizedLevel 2) atTop (𝓝 (etaPhase * ((C : ℂ) / 3))))
    (hLevelFour : Tendsto (normalizedLevel 4) atTop (𝓝 (etaPhase * ((C : ℂ) / 6))))
    (hCross : Tendsto normalizedCross atTop (𝓝 0)) :
    ¬ ∃ L : ℂ, Tendsto (fun N => evenSectorCutoff N 0) atTop (𝓝 L) := by
  obtain ⟨L, hNeg, hLimit⟩ := even_zero_mode_negative_log_limit
    C hC hAggregate hLevelTwo hLevelFour hCross
  refine even_sector_no_ordered_limit_of_log_limit 0 ?_ hLimit
  intro h
  simp [h] at hNeg

end
end ManuscriptAudit.Paper8EvenZeroModeFromEta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenZeroModeFromEta.even_zero_mode_negative_log_limit,
      ``ManuscriptAudit.Paper8EvenZeroModeFromEta.even_zero_mode_no_ordered_limit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
