import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelCutoff
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProgressionMainTermPartition

/-!
# Recovery of the four progression limits from the level and cross-cusp limits

The independently stated analytic inputs are the full-level aggregate,
the two restricted diagonal-level limits, and the vanishing scaled
cross-cusp limit. The conclusion is the four raw progression constants
in the exact conventions of the manuscript sum.
-/

namespace ManuscriptAudit.Paper8ProgressionProfileFromEta

open Filter
open scoped Topology
open Paper8EtaLevelZeroMode (etaPhase)
open Paper8EtaLevelCutoff
open Paper8OddCrossCuspCutoff
open Paper8UnshiftedZeroMode (rawTerm squareRootScale)
open Paper8ProgressionSqrtMainTerm (zeroModeProgressionRaw)
open Paper8ProgressionMainTermPartition (raw_progression_partition)

noncomputable section

def normalizedAggregate (N : ℕ) : ℂ :=
  (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), rawTerm j

def normalizedProgression (r N : ℕ) : ℂ :=
  (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j

def normalizedLevel (L N : ℕ) : ℂ :=
  (squareRootScale N)⁻¹ • levelCutoff L N

def normalizedCross (N : ℕ) : ℂ :=
  (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), crossRaw j

private theorem conjugate_smul (x : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (x • z) = x • (starRingEnd ℂ) z := by
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem normalized_level_four (N : ℕ) :
    normalizedLevel 4 N = etaPhase * (starRingEnd ℂ) (normalizedProgression 0 N) := by
  unfold normalizedLevel normalizedProgression
  rw [levelFourCutoff_eq, conjugate_smul]
  simp only [Complex.real_smul]
  ring

theorem normalized_level_two_sub_four (N : ℕ) :
    normalizedLevel 2 N - normalizedLevel 4 N =
      etaPhase * (starRingEnd ℂ) (normalizedProgression 2 N) := by
  unfold normalizedLevel normalizedProgression
  rw [← smul_sub, levelTwoCutoff_sub_levelFourCutoff_eq, conjugate_smul]
  simp only [Complex.real_smul]
  ring

theorem normalized_cross (N : ℕ) :
    normalizedCross N = (starRingEnd ℂ) (normalizedProgression 1 N - normalizedProgression 3 N) := by
  unfold normalizedCross normalizedProgression
  rw [← smul_sub, crossCutoff_oddProgressionDifference, conjugate_smul]

theorem normalized_progression_partition (N : ℕ) :
    normalizedProgression 0 N + normalizedProgression 1 N +
      normalizedProgression 2 N + normalizedProgression 3 N = normalizedAggregate N := by
  simpa only [normalizedProgression, normalizedAggregate, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, smul_add] using
    congrArg (fun z : ℂ => (squareRootScale N)⁻¹ • z) (raw_progression_partition N)

private theorem conj_tendsto {f : ℕ → ℂ} {a : ℂ} (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun N => (starRingEnd ℂ) (f N)) atTop (𝓝 ((starRingEnd ℂ) a)) :=
  Complex.continuous_conj.continuousAt.tendsto.comp hf

private theorem recover_phase {u v : ℕ → ℂ} {a : ℂ}
    (hEq : ∀ N, u N = etaPhase * (starRingEnd ℂ) (v N))
    (hU : Tendsto u atTop (𝓝 (etaPhase * (starRingEnd ℂ) a))) :
    Tendsto v atTop (𝓝 a) := by
  have hNe : etaPhase ≠ 0 := Complex.exp_ne_zero _
  have hU' : Tendsto (fun N => etaPhase⁻¹ * u N) atTop (𝓝 ((starRingEnd ℂ) a)) := by
    have hConst : Tendsto (fun _ : ℕ => etaPhase⁻¹) atTop (𝓝 etaPhase⁻¹) := tendsto_const_nhds
    simpa only [← mul_assoc, inv_mul_cancel₀ hNe, one_mul] using hConst.mul hU
  have hV : Tendsto (fun N => (starRingEnd ℂ) (etaPhase⁻¹ * u N)) atTop (𝓝 a) := by
    simpa using conj_tendsto hU'
  exact hV.congr (fun N => by rw [hEq N, ← mul_assoc, inv_mul_cancel₀ hNe, one_mul]; simp)

theorem actual_progression_limits_of_level_and_cross (C : ℝ)
    (hAggregate : Tendsto normalizedAggregate atTop (𝓝 (C : ℂ)))
    (hLevelTwo : Tendsto (normalizedLevel 2) atTop (𝓝 (etaPhase * ((C : ℂ) / 3))))
    (hLevelFour : Tendsto (normalizedLevel 4) atTop (𝓝 (etaPhase * ((C : ℂ) / 6))))
    (hCross : Tendsto normalizedCross atTop (𝓝 0)) :
    Tendsto (normalizedProgression 0) atTop (𝓝 ((C : ℂ) / 6)) ∧
    Tendsto (normalizedProgression 1) atTop (𝓝 ((C : ℂ) / 3)) ∧
    Tendsto (normalizedProgression 2) atTop (𝓝 ((C : ℂ) / 6)) ∧
    Tendsto (normalizedProgression 3) atTop (𝓝 ((C : ℂ) / 3)) := by
  have hConj : (starRingEnd ℂ) ((C : ℂ) / 6) = (C : ℂ) / 6 := by
    simp only [map_div₀, Complex.conj_ofReal, map_ofNat]
  have h0 : Tendsto (normalizedProgression 0) atTop (𝓝 ((C : ℂ) / 6)) :=
    recover_phase normalized_level_four (by rw [hConj]; exact hLevelFour)
  have h2 : Tendsto (normalizedProgression 2) atTop (𝓝 ((C : ℂ) / 6)) := by
    apply recover_phase normalized_level_two_sub_four
    rw [hConj]
    have h := hLevelTwo.sub hLevelFour
    have hEq : etaPhase * ((C : ℂ) / 3) - etaPhase * ((C : ℂ) / 6) =
        etaPhase * ((C : ℂ) / 6) := by ring
    rw [hEq] at h
    exact h
  have hOddDiff : Tendsto (fun N => normalizedProgression 1 N - normalizedProgression 3 N)
      atTop (𝓝 0) := by
    have h : Tendsto (fun N => (starRingEnd ℂ) (normalizedCross N)) atTop (𝓝 0) := by
      simpa only [map_zero] using conj_tendsto hCross
    exact h.congr (fun N => by rw [normalized_cross]; simp)
  have hOddSum : Tendsto (fun N => normalizedProgression 1 N + normalizedProgression 3 N)
      atTop (𝓝 (2 * (C : ℂ) / 3)) := by
    have h := hAggregate.sub (h0.add h2)
    have hEq : (C : ℂ) - ((C : ℂ) / 6 + (C : ℂ) / 6) = 2 * (C : ℂ) / 3 := by ring
    rw [hEq] at h
    exact h.congr fun N => by rw [← normalized_progression_partition N]; ring
  have h1 : Tendsto (normalizedProgression 1) atTop (𝓝 ((C : ℂ) / 3)) := by
    have h := (hOddSum.add hOddDiff).div_const 2
    have hEq : (2 * (C : ℂ) / 3 + 0) / 2 = (C : ℂ) / 3 := by ring
    rw [hEq] at h
    exact h.congr fun N => by ring
  have h3 : Tendsto (normalizedProgression 3) atTop (𝓝 ((C : ℂ) / 3)) := by
    have h := (hOddSum.sub hOddDiff).div_const 2
    have hEq : (2 * (C : ℂ) / 3 - 0) / 2 = (C : ℂ) / 3 := by ring
    rw [hEq] at h
    exact h.congr fun N => by ring
  exact ⟨h0, h1, h2, h3⟩

end
end ManuscriptAudit.Paper8ProgressionProfileFromEta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ProgressionProfileFromEta.normalized_level_four,
      ``ManuscriptAudit.Paper8ProgressionProfileFromEta.normalized_level_two_sub_four,
      ``ManuscriptAudit.Paper8ProgressionProfileFromEta.normalized_cross,
      ``ManuscriptAudit.Paper8ProgressionProfileFromEta.normalized_progression_partition,
      ``ManuscriptAudit.Paper8ProgressionProfileFromEta.actual_progression_limits_of_level_and_cross] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
