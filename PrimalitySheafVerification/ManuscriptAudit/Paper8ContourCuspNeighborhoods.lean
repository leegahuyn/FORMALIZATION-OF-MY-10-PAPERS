import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8LowerContourLimits

/-!
# No common contour limit in actual half-plane cusp neighborhoods

Both residue readings are covered at arbitrary real part of z. The
comparison excludes agreement of ordered limits and leaves separate
convergence as a distinct arithmetic question.
-/

namespace ManuscriptAudit.Paper8ContourCuspNeighborhoods

open Filter Metric Set
open scoped Topology
open Paper8HolomorphicPartPhase (qParameter)
open Paper8ContourResidueWeights (reducedResidues)
open Paper8LiteralContourLimits (printedOuterPartialSum printedOuterPartialSum_eq)
open Paper8SeparateContourSeries (orderedOuterPartialSum)
open Paper8ContourAnalyticDifference (normalizedDifference normalized_at_zero normalized_continuousAt_zero)
open Paper8ContourSignedCoefficient (reduced_difference_summable_and_positive)
open Paper8ContourAllResidueSign (all_difference_real_negative)

noncomputable section

def CommonOrderedLimit (S : ∀ k : ℕ, Finset (Fin (2 * k))) (z : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 S z) atTop (𝓝 L) ∧
    Tendsto (printedOuterPartialSum (2 / 3) 16 S z) atTop (𝓝 L)

private theorem upper_normalized_near_zero (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    (h : normalizedDifference S 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ Q ∈ ball (0 : ℂ) r, normalizedDifference S Q ≠ 0 := by
  have hOpen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hZero : normalizedDifference S 0 ∈ ({0}ᶜ : Set ℂ) := by
    change normalizedDifference S 0 ∉ ({0} : Set ℂ)
    simpa only [Set.mem_singleton_iff] using h
  have hSet : normalizedDifference S ⁻¹' ({0}ᶜ : Set ℂ) ∈ 𝓝 (0 : ℂ) :=
    (normalized_continuousAt_zero S).tendsto (hOpen.mem_nhds hZero)
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hSet
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro Q hQ
  have hQ' : Q ∈ ball (0 : ℂ) r := by
    rw [mem_ball] at hQ ⊢
    exact hQ.trans_le (min_le_left _ _)
  have hNZ := hBall hQ'
  change normalizedDifference S Q ∉ ({0} : Set ℂ) at hNZ
  simpa only [Set.mem_singleton_iff] using hNZ

private theorem upper_no_common_at_nome (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ}
    (hq : ‖qParameter z‖ ≤ 1 / 4) (hn : normalizedDifference S (qParameter z) ≠ 0) :
    ¬ CommonOrderedLimit S z := by
  have hP : printedOuterPartialSum 23 24 S z = orderedOuterPartialSum 23 24 S (qParameter z) :=
    funext (printedOuterPartialSum_eq 23 (by norm_num) le_rfl S hq)
  have hL : printedOuterPartialSum (2 / 3) 16 S z = orderedOuterPartialSum (2 / 3) 16 S (qParameter z) :=
    funext (printedOuterPartialSum_eq (2 / 3) (by norm_num) (by norm_num) S hq)
  unfold CommonOrderedLimit
  rw [hP, hL]
  apply Paper8SeparateContourSeries.no_common_ordered_outer_limit S hq
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : qParameter z ≠ 0 := Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero hp hz) hn

theorem no_common_ordered_limit_near_upper_cusp :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖qParameter z‖ < r →
      ¬ CommonOrderedLimit reducedResidues z ∧ ¬ CommonOrderedLimit (fun _ => Finset.univ) z := by
  have hRed : 0 < (normalizedDifference reducedResidues 0).re := by
    rw [normalized_at_zero]
    exact reduced_difference_summable_and_positive.2
  have hAll : (normalizedDifference (fun _ => Finset.univ) 0).re < 0 := by
    rw [normalized_at_zero]
    exact all_difference_real_negative
  have hR0 : normalizedDifference reducedResidues 0 ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hRed
    exact (lt_irrefl 0) hRed
  have hA0 : normalizedDifference (fun _ => Finset.univ) 0 ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hAll
    exact (lt_irrefl 0) hAll
  obtain ⟨rR, hrR, h4R, hR⟩ := upper_normalized_near_zero reducedResidues hR0
  obtain ⟨rA, hrA, _, hA⟩ := upper_normalized_near_zero (fun _ => Finset.univ) hA0
  refine ⟨min rR rA, lt_min hrR hrA, ?_⟩
  intro z hz
  have hNR := hz.trans_le (min_le_left _ _)
  have hNA := hz.trans_le (min_le_right _ _)
  have h4 : ‖qParameter z‖ ≤ 1 / 4 := hNR.le.trans h4R
  exact ⟨upper_no_common_at_nome reducedResidues h4
      (hR _ (by rwa [mem_ball, dist_zero_right])),
    upper_no_common_at_nome (fun _ => Finset.univ) h4
      (hA _ (by rwa [mem_ball, dist_zero_right]))⟩

theorem no_common_ordered_limit_near_lower_cusp :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z.im < 0 → ‖qParameter (-z)‖ < r →
      ¬ CommonOrderedLimit reducedResidues z ∧ ¬ CommonOrderedLimit (fun _ => Finset.univ) z := by
  obtain ⟨rR, hrR, h4R, hR⟩ := Paper8LowerContourAnalyticDifference.reduced_outerDifference_real_positive_near_zero
  obtain ⟨rA, hrA, _, hA⟩ := Paper8LowerContourAnalyticDifference.all_outerDifference_real_positive_near_zero
  refine ⟨min rR rA, lt_min hrR hrA, ?_⟩
  intro z hz hq
  have hNR := hq.trans_le (min_le_left _ _)
  have hNA := hq.trans_le (min_le_right _ _)
  have h4 : ‖qParameter (-z)‖ ≤ 1 / 4 := hNR.le.trans h4R
  refine ⟨Paper8LowerContourLimits.no_common_printed_ordered_limit reducedResidues hz h4 ?_,
    Paper8LowerContourLimits.no_common_printed_ordered_limit (fun _ => Finset.univ) hz h4 ?_⟩
  · intro h
    have hh := hR _ (by rwa [mem_ball, dist_zero_right])
    rw [h, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  · intro h
    have hh := hA _ (by rwa [mem_ball, dist_zero_right])
    rw [h, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh

end
end ManuscriptAudit.Paper8ContourCuspNeighborhoods

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourCuspNeighborhoods.no_common_ordered_limit_near_upper_cusp,
      ``ManuscriptAudit.Paper8ContourCuspNeighborhoods.no_common_ordered_limit_near_lower_cusp] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
