import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparateReciprocalContourSeries
import PrimalitySheafVerification.ManuscriptAudit.Paper8LowerContourParameterLink
import PrimalitySheafVerification.ManuscriptAudit.Paper8LiteralContourLimits

/-! Exact arithmetic convergence criterion for the two separate printed lower contour sums. -/

namespace ManuscriptAudit.Paper8SeparatePrintedLowerContours

open Filter
open scoped Topology
open Paper8HolomorphicPartPhase (qParameter)
open Paper8ContourResidueWeights (prefactor residueWeight)
open Paper8LocalContour (root phi)
open Paper8FixedContourDifference (phiAtQ)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8LiteralContourLimits (printedScalar printedScalar_eq printedOuterPartialSum)
open Paper8LowerContourParameterLink (nome_mul_phi_eq_inverse_nome)
open Paper8SeparateReciprocalContourSeries
  (sumKernel commonTerm separateTerm separate_ordered_convergence_iff_common)

noncomputable section

private theorem printed_term_eq (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) {z : ℂ}
    (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    prefactor k * (∑ d ∈ S k, printedScalar z k d * phi α β k (d.val : ℤ) z) =
      separateTerm (β - α) β S k (qParameter (-z)) := by
  unfold separateTerm sumKernel
  rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  apply congrArg (fun w : ℂ => prefactor k * w)
  refine Finset.sum_congr rfl fun d _ => ?_
  change printedScalar z k d * phi α β k (d.val : ℤ) z =
      -(residueWeight k d * ((root k ^ (d.val : ℤ))⁻¹ *
        phiAtQ (-(β - α)) (-β) k (root k ^ (d.val : ℤ))⁻¹ (qParameter (-z))))
  have hA : -(β - α) = α - β := by ring
  rw [printedScalar_eq, mul_assoc, nome_mul_phi_eq_inverse_nome α hβ hβ' hk (d.val : ℤ) hz hq, hA]
  ring

theorem printed_partial_sum_eq (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ} (hz : z.im < 0)
    (hq : ‖qParameter (-z)‖ ≤ 1 / 4) (N : ℕ) :
    printedOuterPartialSum α β S z N =
      1 + (Real.pi : ℂ) * orderedPartialSum
        (fun n => separateTerm (β - α) β S (n + 1) (qParameter (-z))) N := by
  unfold printedOuterPartialSum orderedPartialSum
  apply congrArg (fun w : ℂ => 1 + (Real.pi : ℂ) * w)
  exact Finset.sum_congr rfl (fun n _ => printed_term_eq α hβ hβ' S (Nat.succ_pos n) hz hq)

private theorem affine_ordered_convergence_iff (f : ℕ → ℂ) :
    (∃ L : ℂ, Tendsto (fun n => 1 + (Real.pi : ℂ) * f n) atTop (𝓝 L)) ↔
      ∃ L : ℂ, Tendsto f atTop (𝓝 L) := by
  have hOne : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  have hPi : Tendsto (fun _ : ℕ => (Real.pi : ℂ)) atTop (𝓝 (Real.pi : ℂ)) := tendsto_const_nhds
  have hInv : Tendsto (fun _ : ℕ => (Real.pi : ℂ)⁻¹) atTop (𝓝 ((Real.pi : ℂ)⁻¹)) := tendsto_const_nhds
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨(L - 1) * (Real.pi : ℂ)⁻¹, ((hL.sub hOne).mul hInv).congr fun n => ?_⟩
    change ((1 + (Real.pi : ℂ) * f n) - 1) * (Real.pi : ℂ)⁻¹ = f n
    field_simp [hp] <;> ring
  · rintro ⟨L, hL⟩
    exact ⟨1 + (Real.pi : ℂ) * L, hOne.add (hPi.mul hL)⟩

theorem printed_ordered_convergence_iff_common (α : ℝ) {β : ℝ} (hβ : 0 < β)
    (hβ' : β ≤ 24) (hα : 0 ≤ β - α) (hα' : β - α ≤ 24)
    (S : ∀ k : ℕ, Finset (Fin (2 * k))) {z : ℂ} (hz : z.im < 0)
    (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    (∃ L : ℂ, Tendsto (printedOuterPartialSum α β S z) atTop (𝓝 L)) ↔
      ∃ L : ℂ, Tendsto (orderedPartialSum (fun n => commonTerm S (n + 1) (qParameter (-z)))) atTop (𝓝 L) := by
  have hFun : printedOuterPartialSum α β S z =
      (fun N => 1 + (Real.pi : ℂ) * orderedPartialSum
        (fun n => separateTerm (β - α) β S (n + 1) (qParameter (-z))) N) :=
    funext (printed_partial_sum_eq α hβ hβ' S hz hq)
  rw [hFun, affine_ordered_convergence_iff]
  exact separate_ordered_convergence_iff_common hα hα' hβ.le hβ' S hq

theorem printed_primary_and_literal_ordered_convergence_iff (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    {z : ℂ} (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    (∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 S z) atTop (𝓝 L)) ↔
      ∃ L : ℂ, Tendsto (printedOuterPartialSum (2 / 3) 16 S z) atTop (𝓝 L) := by
  exact (printed_ordered_convergence_iff_common 23 (by norm_num) le_rfl
    (by norm_num) (by norm_num) S hz hq).trans
      (printed_ordered_convergence_iff_common (2 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) S hz hq).symm

end
end ManuscriptAudit.Paper8SeparatePrintedLowerContours

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SeparatePrintedLowerContours.printed_partial_sum_eq,
      ``ManuscriptAudit.Paper8SeparatePrintedLowerContours.printed_ordered_convergence_iff_common,
      ``ManuscriptAudit.Paper8SeparatePrintedLowerContours.printed_primary_and_literal_ordered_convergence_iff] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
