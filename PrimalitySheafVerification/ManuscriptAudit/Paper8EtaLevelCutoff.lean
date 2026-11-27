import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProgressionSqrtMainTerm

/-!
# Attachment to the manuscript's actual progression cutoffs

The level-four cutoff is the 0 mod 4 raw progression. The difference
of the level-two and level-four cutoffs is the 2 mod 4 raw progression.
The manuscript's sign convention requires conjugation and the finite
Kloosterman normalization contributes the universal eta phase.
-/

namespace ManuscriptAudit.Paper8EtaLevelCutoff

open Paper8EtaLevelZeroMode
open Paper8UnshiftedZeroMode (rawTerm)
open Paper8ProgressionSqrtMainTerm (zeroModeProgressionRaw)
open Paper8DedekindZeroReference (referenceZeroSum reducedFrequencySum_zero_eq_conj)

noncomputable section

def levelRaw (level j : ℕ) : ℂ :=
  levelSum level (Nat.succ_pos j) / ((j + 1 : ℕ) : ℂ)

def levelCutoff (level N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), levelRaw level j

private theorem conjugate_raw (j : ℕ) :
    (starRingEnd ℂ) (rawTerm j) = referenceZeroSum (j + 1) / ((j + 1 : ℕ) : ℂ) := by
  rw [rawTerm, reducedFrequencySum_zero_eq_conj, map_div₀]
  simp

theorem levelFourRaw_eq (j : ℕ) :
    levelRaw 4 j = etaPhase * (starRingEnd ℂ) (zeroModeProgressionRaw 0 j) := by
  unfold levelRaw zeroModeProgressionRaw
  rw [levelFour_eq_progression_zero]
  by_cases h : (j + 1) % 4 = 0
  · simp only [h, if_true, conjugate_raw, mul_div_assoc]
  · simp [h]

theorem levelTwoRaw_sub_levelFourRaw_eq (j : ℕ) :
    levelRaw 2 j - levelRaw 4 j =
      etaPhase * (starRingEnd ℂ) (zeroModeProgressionRaw 2 j) := by
  unfold levelRaw zeroModeProgressionRaw
  rw [← sub_div, levelTwo_sub_levelFour_eq_progression_two]
  by_cases h : (j + 1) % 4 = 2
  · simp only [h, if_true, conjugate_raw, mul_div_assoc]
  · simp [h]

theorem levelFourCutoff_eq (N : ℕ) :
    levelCutoff 4 N = etaPhase * (starRingEnd ℂ)
      (∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw 0 j) := by
  rw [levelCutoff, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => levelFourRaw_eq j)

theorem levelTwoCutoff_sub_levelFourCutoff_eq (N : ℕ) :
    levelCutoff 2 N - levelCutoff 4 N = etaPhase * (starRingEnd ℂ)
      (∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw 2 j) := by
  simp only [levelCutoff]
  rw [← Finset.sum_sub_distrib, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => levelTwoRaw_sub_levelFourRaw_eq j)

end
end ManuscriptAudit.Paper8EtaLevelCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaLevelCutoff.levelFourRaw_eq,
      ``ManuscriptAudit.Paper8EtaLevelCutoff.levelTwoRaw_sub_levelFourRaw_eq,
      ``ManuscriptAudit.Paper8EtaLevelCutoff.levelFourCutoff_eq,
      ``ManuscriptAudit.Paper8EtaLevelCutoff.levelTwoCutoff_sub_levelFourCutoff_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
