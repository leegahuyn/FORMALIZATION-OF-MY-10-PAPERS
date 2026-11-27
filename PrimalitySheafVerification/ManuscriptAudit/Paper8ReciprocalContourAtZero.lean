import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalContourSign

/-! The signed reciprocal moments are the actual fixed inverse-nome contour differences at zero. -/

namespace ManuscriptAudit.Paper8ReciprocalContourAtZero

open Paper8ContourResidueWeights (prefactor residueWeight reducedResidues)
open Paper8LocalContour (root)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular_at_zero)
open Paper8FixedContourDifference (phiAtQ)
open Paper8ContourMoment (atZero atZero_eq_its_real_part)
open Paper8ReciprocalContourMoment (momentDifference)
open Paper8ReciprocalContourSign
  (signedMoment inverseWeight reduced_signedMoment_summable_and_real_positive
    all_signedMoment_summable_and_real_positive)

noncomputable section

def inverseNomeTerm (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (Q : ℂ) : ℂ :=
  -prefactor k * ∑ d ∈ S k, residueWeight k d * (root k ^ (d.val : ℤ))⁻¹ *
    (phiAtQ (-1) (-24) k (root k ^ (d.val : ℤ))⁻¹ Q -
      phiAtQ (-46 / 3) (-16) k (root k ^ (d.val : ℤ))⁻¹ Q)

private theorem phi_zero (α β : ℝ) (k : ℕ) (ζ : ℂ) :
    phiAtQ α β k ζ 0 = atZero α k fixedRadius := by
  simp only [phiAtQ, atZero, regular_at_zero]

theorem inverseNomeTerm_zero (S : ∀ k : ℕ, Finset (Fin (2 * k))) (n : ℕ) :
    inverseNomeTerm S (n + 1) 0 = signedMoment S fixedRadius n := by
  have hDiff (ζ : ℂ) :
      phiAtQ (-1) (-24) (n + 1) ζ 0 - phiAtQ (-46 / 3) (-16) (n + 1) ζ 0 =
        (momentDifference (n + 1) fixedRadius : ℂ) := by
    rw [phi_zero (-1) (-24), phi_zero (-46 / 3) (-16), momentDifference, Complex.ofReal_sub]
    exact congrArg₂ (· - ·)
      (atZero_eq_its_real_part (Nat.succ_pos n) (-1) fixedRadius_pos)
      (atZero_eq_its_real_part (Nat.succ_pos n) (-46 / 3) fixedRadius_pos)
  unfold inverseNomeTerm signedMoment inverseWeight
  simp_rw [hDiff, ← Finset.sum_mul]
  ring

theorem reduced_inverseNomeTerm_zero_summable_and_positive :
    Summable (fun n : ℕ => ‖inverseNomeTerm reducedResidues (n + 1) 0‖) ∧
      0 < (∑' n : ℕ, inverseNomeTerm reducedResidues (n + 1) 0).re := by
  simp_rw [inverseNomeTerm_zero]
  exact reduced_signedMoment_summable_and_real_positive fixedRadius_pos

theorem all_inverseNomeTerm_zero_summable_and_positive :
    Summable (fun n : ℕ => ‖inverseNomeTerm (fun _ => Finset.univ) (n + 1) 0‖) ∧
      0 < (∑' n : ℕ, inverseNomeTerm (fun _ => Finset.univ) (n + 1) 0).re := by
  simp_rw [inverseNomeTerm_zero]
  exact all_signedMoment_summable_and_real_positive fixedRadius_pos

end
end ManuscriptAudit.Paper8ReciprocalContourAtZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalContourAtZero.inverseNomeTerm_zero,
      ``ManuscriptAudit.Paper8ReciprocalContourAtZero.reduced_inverseNomeTerm_zero_summable_and_positive,
      ``ManuscriptAudit.Paper8ReciprocalContourAtZero.all_inverseNomeTerm_zero_summable_and_positive] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
