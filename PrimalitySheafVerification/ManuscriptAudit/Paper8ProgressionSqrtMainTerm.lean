import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenCutoffLogLimit
import PrimalitySheafVerification.ManuscriptAudit.Paper8SqrtAbelLogTransfer

/-!
# The exact mode-zero input to the signed even logarithmic asymptotic

A square-root asymptotic for each raw reduced progression gives a
logarithmic asymptotic for the actual weighted progression. The
result then sums the four limiting even-gcd weights. Each raw
progression limit remains explicit.
-/

namespace ManuscriptAudit.Paper8ProgressionSqrtMainTerm

open Filter
open scoped Topology
open Paper8CutoffLog (cutoffLog cutoffLog_pos cutoffLog_tendsto_atTop)
open Paper8ContourGammaSeries (coefficient)
open Paper8UnshiftedZeroMode (squareRootScale rawTerm sqrt_smul_coefficient)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8EvenGcdOrderedLimit (progressionPartialSum unshiftedCoefficient evenSectorCutoff evenWeight)
open Paper8SqrtAbelLogTransfer (normalized_abel_sum_log_limit)
open Paper8EvenCutoffLogLimit (even_sector_log_limit)

noncomputable section

def zeroModeProgressionRaw (r j : ℕ) : ℂ :=
  if (j + 1) % 4 = r then rawTerm j else 0

private theorem cutoffLog_succ_ratio :
    Tendsto (fun N => cutoffLog N / cutoffLog (N + 1)) atTop (𝓝 1) := by
  have hAt : Tendsto (fun N : ℕ => N + 2) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun N hN => ?_
    change b ≤ N + 2
    omega
  have hShift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun N hN => ?_
    exact hN.trans (Nat.le_succ N)
  have hD : Tendsto (fun N => cutoffLog (N + 1) - cutoffLog N) atTop (𝓝 0) := by
    refine (Real.tendsto_log_nat_add_one_sub_log.comp hAt).congr fun N => ?_
    have ha : ((N + 2 : ℕ) : ℝ) + 1 = (((N + 1) + 2 : ℕ) : ℝ) := by push_cast; ring
    change Real.log (((N + 2 : ℕ) : ℝ) + 1) - cutoffLog N = _
    simp only [ha, cutoffLog]
  have hInv : Tendsto (fun N => (cutoffLog (N + 1))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp cutoffLog_tendsto_atTop).comp hShift
  have hP : Tendsto (fun N => (cutoffLog (N + 1) - cutoffLog N) / cutoffLog (N + 1))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hD.mul hInv
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hOne.sub hP
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  field_simp [(cutoffLog_pos (N + 1)).ne'] <;> ring

theorem progression_zero_log_limit_of_sqrt_main_term (r : ℕ) {A : ℂ}
    (hA : Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j) atTop (𝓝 A)) :
    Tendsto (fun N => (cutoffLog N)⁻¹ •
        progressionPartialSum (fun D => unshiftedCoefficient D 0) r N)
      atTop (𝓝 ((1 / 2 : ℝ) • (-(coefficient 1 0 : ℂ) * A))) := by
  let g (j : ℕ) := -(coefficient 1 0 : ℂ) * zeroModeProgressionRaw r j
  let V (N : ℕ) := progressionPartialSum (fun D => unshiftedCoefficient D 0) r N
  have hInput : Tendsto (fun N => (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), g j)
      atTop (𝓝 (-(coefficient 1 0 : ℂ) * A)) := by
    refine (tendsto_const_nhds.mul hA).congr fun N => ?_
    change -(coefficient 1 0 : ℂ) * ((squareRootScale N)⁻¹ •
      (∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j)) =
        (squareRootScale N)⁻¹ • ∑ j ∈ Finset.range (N + 1), g j
    unfold g
    rw [← Finset.mul_sum]
    simp only [Complex.real_smul]
    ring
  have hTerm (j : ℕ) : g j = squareRootScale j •
      (if (j + 1) % 4 = r then unshiftedCoefficient (j + 1) 0 else 0) := by
    unfold g zeroModeProgressionRaw
    by_cases h : (j + 1) % 4 = r
    · rw [if_pos h, if_pos h, sqrt_smul_coefficient]
    · rw [if_neg h, if_neg h, mul_zero, smul_zero]
  have hEq (N : ℕ) : (∑ j ∈ Finset.range (N + 1), (squareRootScale j)⁻¹ • g j) = V (N + 1) := by
    unfold V progressionPartialSum orderedPartialSum
    refine Finset.sum_congr rfl fun j _ => ?_
    have hPos : 0 < squareRootScale j := Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos j))
    rw [hTerm, smul_smul, inv_mul_cancel₀ hPos.ne', one_smul]
  have h0 : Tendsto (fun N => (cutoffLog N)⁻¹ • V (N + 1))
      atTop (𝓝 ((1 / 2 : ℝ) • (-(coefficient 1 0 : ℂ) * A))) :=
    (normalized_abel_sum_log_limit g hInput).congr fun N => by rw [hEq]
  apply (tendsto_add_atTop_iff_nat 1).1
  have h1 := cutoffLog_succ_ratio.smul h0
  rw [one_smul] at h1
  refine h1.congr fun N => ?_
  rw [smul_smul]
  have he : (cutoffLog N / cutoffLog (N + 1)) * (cutoffLog N)⁻¹ =
      (cutoffLog (N + 1))⁻¹ := by
    field_simp [(cutoffLog_pos N).ne', (cutoffLog_pos (N + 1)).ne'] <;> ring
  rw [he]

theorem even_zero_mode_log_limit_of_sqrt_main_terms (A : ℕ → ℂ)
    (hA : ∀ r ∈ Finset.range 4, Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j) atTop (𝓝 (A r))) :
    Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N 0) atTop
      (𝓝 (∑ r ∈ Finset.range 4,
        (∑' h : ℕ, evenWeight (h + 1) r) * ((1 / 2 : ℝ) • (-(coefficient 1 0 : ℂ) * A r)))) :=
  even_sector_log_limit 0 (fun r => (1 / 2 : ℝ) • (-(coefficient 1 0 : ℂ) * A r))
    (fun r hr => progression_zero_log_limit_of_sqrt_main_term r (hA r hr))

end
end ManuscriptAudit.Paper8ProgressionSqrtMainTerm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ProgressionSqrtMainTerm.progression_zero_log_limit_of_sqrt_main_term,
      ``ManuscriptAudit.Paper8ProgressionSqrtMainTerm.even_zero_mode_log_limit_of_sqrt_main_terms] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
