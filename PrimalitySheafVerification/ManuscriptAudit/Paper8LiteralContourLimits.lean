import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourParameterLink
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparateContourSeries

/-!
# The native ordered limit obstruction in the literal contour variables

Physical p. 335 prints the Dedekind multiplier and the exponential
containing z inside the finite residue sum. Factoring out the nome and
changing to the fixed admissible radius gives the ordered sums already
compared in the q-variable.
-/

namespace ManuscriptAudit.Paper8LiteralContourLimits

open Filter Set
open scoped Topology
open Paper8ContourResidueWeights (dedekindSum firstPhase residueWeight prefactor reducedResidues)
open Paper8LocalContour (root phi)
open Paper8HolomorphicPartPhase (periodCoefficient qParameter)
open Paper8ContourParameterLink
  (fixed_phi_eq_local_small_radius_phi positive_real_nome_has_upper_half_plane_parameter)
open Paper8FixedContourDifference (phiAtQ)
open Paper8SeparateContourSeries
  (orderedPartialSum orderedOuterPartialSum separateTerm no_common_ordered_outer_limit_small_positive_q)

noncomputable section

def printedScalar (z : ℂ) (k : ℕ) (d : Fin (2 * k)) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I *
    ((dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) : ℂ)) *
  Complex.exp (periodCoefficient *
    (-(d.val : ℂ) / 8 * (1 + (-1 : ℂ) ^ k) + (d.val : ℂ) / (2 * (k : ℂ)) + z))

theorem printedScalar_eq (z : ℂ) (k : ℕ) (d : Fin (2 * k)) :
    printedScalar z k d = residueWeight k d * qParameter z := by
  rw [printedScalar, residueWeight, qParameter, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold firstPhase periodCoefficient
  push_cast
  ring

def printedOuterPartialSum (α β : ℝ) (S : ∀ k : ℕ, Finset (Fin (2 * k))) (z : ℂ) (N : ℕ) : ℂ :=
  1 + (Real.pi : ℂ) * ∑ n ∈ Finset.range N, prefactor (n + 1) *
    ∑ d ∈ S (n + 1), printedScalar z (n + 1) d * phi α β (n + 1) (d.val : ℤ) z

private theorem printed_sum_term_eq (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) {z : ℂ}
    (hq : ‖qParameter z‖ ≤ 1 / 4) :
    prefactor k * (∑ d ∈ S k, printedScalar z k d * phi α β k (d.val : ℤ) z) =
      qParameter z * separateTerm α β S k (qParameter z) := by
  change prefactor k * (∑ d ∈ S k, printedScalar z k d * phi α β k (d.val : ℤ) z) =
    qParameter z * (prefactor k * ∑ d ∈ S k, residueWeight k d *
      phiAtQ α β k (root k ^ (d.val : ℤ)) (qParameter z))
  have hMul : qParameter z * (∑ d ∈ S k, residueWeight k d *
      phiAtQ α β k (root k ^ (d.val : ℤ)) (qParameter z)) =
    ∑ d ∈ S k, qParameter z * (residueWeight k d *
      phiAtQ α β k (root k ^ (d.val : ℤ)) (qParameter z)) := by rw [Finset.mul_sum]
  rw [mul_left_comm (qParameter z) (prefactor k), hMul]
  apply congrArg (fun w : ℂ => prefactor k * w)
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [printedScalar_eq, fixed_phi_eq_local_small_radius_phi α hβ hβ' hk (d.val : ℤ) hq]
  ring

theorem printedOuterPartialSum_eq (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ} (hq : ‖qParameter z‖ ≤ 1 / 4) (N : ℕ) :
    printedOuterPartialSum α β S z N = orderedOuterPartialSum α β S (qParameter z) N := by
  unfold printedOuterPartialSum orderedOuterPartialSum orderedPartialSum
  have hMul : qParameter z * (∑ n ∈ Finset.range N, separateTerm α β S (n + 1) (qParameter z)) =
      ∑ n ∈ Finset.range N, qParameter z * separateTerm α β S (n + 1) (qParameter z) := by
    rw [Finset.mul_sum]
  rw [mul_assoc (Real.pi : ℂ) (qParameter z), hMul]
  apply congrArg (fun w : ℂ => 1 + (Real.pi : ℂ) * w)
  exact Finset.sum_congr rfl (fun n _ => printed_sum_term_eq α hβ hβ' S (Nat.succ_pos n) hq)

theorem no_common_printed_ordered_limit_at_upper_half_plane_parameters :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Ioo (0 : ℝ) r, ∃ z : ℂ, 0 < z.im ∧ qParameter z = (q : ℂ) ∧
      (¬ ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 reducedResidues z) atTop (𝓝 L) ∧
        Tendsto (printedOuterPartialSum (2 / 3) 16 reducedResidues z) atTop (𝓝 L)) ∧
      (¬ ∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 (fun _ => Finset.univ) z) atTop (𝓝 L) ∧
        Tendsto (printedOuterPartialSum (2 / 3) 16 (fun _ => Finset.univ) z) atTop (𝓝 L)) := by
  obtain ⟨r, hr, hNone⟩ := no_common_ordered_outer_limit_small_positive_q
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), ?_⟩
  intro q hq
  have hqr : q < r := hq.2.trans_le (min_le_left _ _)
  have hq4 : q ≤ 1 / 4 := hq.2.le.trans (min_le_right _ _)
  obtain ⟨z, hz, hNome⟩ := positive_real_nome_has_upper_half_plane_parameter hq.1
    (hq4.trans_lt (by norm_num))
  have hZ4 : ‖qParameter z‖ ≤ 1 / 4 := by
    rw [hNome, Complex.norm_real, Real.norm_of_nonneg hq.1.le]
    exact hq4
  have hPrimary (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
      printedOuterPartialSum 23 24 S z = orderedOuterPartialSum 23 24 S (q : ℂ) := by
    funext N
    rw [printedOuterPartialSum_eq 23 (by norm_num) le_rfl S hZ4 N, hNome]
  have hLiteral (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
      printedOuterPartialSum (2 / 3) 16 S z = orderedOuterPartialSum (2 / 3) 16 S (q : ℂ) := by
    funext N
    rw [printedOuterPartialSum_eq (2 / 3) (by norm_num) (by norm_num) S hZ4 N, hNome]
  refine ⟨z, hz, hNome, ?_⟩
  simp only [hPrimary, hLiteral]
  exact hNone q ⟨hq.1, hqr⟩

end
end ManuscriptAudit.Paper8LiteralContourLimits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LiteralContourLimits.printedScalar_eq,
      ``ManuscriptAudit.Paper8LiteralContourLimits.printedOuterPartialSum_eq,
      ``ManuscriptAudit.Paper8LiteralContourLimits.no_common_printed_ordered_limit_at_upper_half_plane_parameters] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
