import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueFiniteCutoff

/-!
# Reduction of a literal ordered mode limit to its even sector

At each Fourier mode the checked odd rescaling transfers any
ordered reduced-residue limit. The literal all-residue mode then
has an ordered limit exactly when the remaining even sector does.
-/

namespace ManuscriptAudit.Paper8AllResidueModeConvergence

open Filter
open scoped Topology
open Paper8ContourResidueWeights (reducedResidues)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8ReciprocalCommonFourier (fourierCoefficient orderedFourierCoefficient)
open Paper8EvenGcdOrderedLimit (evenSectorCutoff)
open Paper8OddGcdOrderedLimit (oddScale oddScale_norm_summable
  odd_divided_sum_eq_finite weighted_divided_partial_limits)
open Paper8AllResidueFiniteCutoff (finite_all_residue_fourier_cutoff sum_range_add_one_eq_Icc)

noncomputable section

def oddSectorCutoff (N n : ℕ) : ℂ :=
  ∑ g ∈ (Finset.Icc 1 N).filter Odd, ∑ D ∈ Finset.Icc 1 (N / g),
    oddScale g * fourierCoefficient reducedResidues D n

theorem odd_sector_cutoff_eq_tsum (N n : ℕ) :
    oddSectorCutoff N n = ∑' j : ℕ, oddScale (j + 1) *
      orderedFourierCoefficient reducedResidues (N / (j + 1)) n := by
  change oddSectorCutoff N n = ∑' j : ℕ, oddScale (j + 1) *
    orderedPartialSum (fun k => fourierCoefficient reducedResidues (k + 1) n) (N / (j + 1))
  rw [odd_divided_sum_eq_finite]
  rw [sum_range_add_one_eq_Icc N (fun g => oddScale g *
    orderedPartialSum (fun k => fourierCoefficient reducedResidues (k + 1) n) (N / g))]
  unfold oddSectorCutoff
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : Odd g
  · rw [if_pos hg, orderedPartialSum, Finset.mul_sum,
      sum_range_add_one_eq_Icc (N / g) (fun D => oddScale g * fourierCoefficient reducedResidues D n)]
  · simp only [if_neg hg, oddScale, zero_mul]

theorem odd_sector_mode_limit_of_reduced (n : ℕ) {L : ℂ}
    (hL : Tendsto (fun N => orderedFourierCoefficient reducedResidues N n) atTop (𝓝 L)) :
    Tendsto (fun N => oddSectorCutoff N n) atTop (𝓝 (∑' j : ℕ, oddScale (j + 1) * L)) := by
  have h := weighted_divided_partial_limits (fun N => orderedFourierCoefficient reducedResidues N n)
    (fun j => oddScale (j + 1)) hL oddScale_norm_summable
  exact h.congr fun N => (odd_sector_cutoff_eq_tsum N n).symm

theorem all_residue_mode_limit_iff_even (n : ℕ) {L : ℂ}
    (hL : Tendsto (fun N => orderedFourierCoefficient reducedResidues N n) atTop (𝓝 L)) (B : ℂ) :
    Tendsto (fun N => orderedFourierCoefficient (fun _ => Finset.univ) N n) atTop (𝓝 B) ↔
      Tendsto (fun N => evenSectorCutoff N n) atTop
        (𝓝 (B - ∑' j : ℕ, oddScale (j + 1) * L)) := by
  let A : ℂ := ∑' j : ℕ, oddScale (j + 1) * L
  have hOdd : Tendsto (fun N => oddSectorCutoff N n) atTop (𝓝 A) :=
    odd_sector_mode_limit_of_reduced n hL
  have hCut (N : ℕ) : orderedFourierCoefficient (fun _ => Finset.univ) N n =
      oddSectorCutoff N n + evenSectorCutoff N n := finite_all_residue_fourier_cutoff N n
  constructor
  · intro h
    refine (h.sub hOdd).congr fun N => ?_
    change orderedFourierCoefficient (fun _ => Finset.univ) N n - oddSectorCutoff N n =
      evenSectorCutoff N n
    rw [hCut, add_comm (oddSectorCutoff N n), add_sub_cancel_right]
  · intro h
    have h' := hOdd.add h
    change Tendsto _ atTop (𝓝 (A + (B - A))) at h'
    rw [add_comm A, sub_add_cancel] at h'
    exact h'.congr fun N => (hCut N).symm

end
end ManuscriptAudit.Paper8AllResidueModeConvergence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8AllResidueModeConvergence.odd_sector_cutoff_eq_tsum,
      ``ManuscriptAudit.Paper8AllResidueModeConvergence.odd_sector_mode_limit_of_reduced,
      ``ManuscriptAudit.Paper8AllResidueModeConvergence.all_residue_mode_limit_iff_even] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
