import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaDedekindMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode

/-! Actual eta principal multipliers in the finite same-cusp zero-mode sums. -/

namespace ManuscriptAudit.Paper8ActualEtaLevelSums

open Paper8ActualEtaDedekindMultiplier Paper8EtaPositiveLowerLeftMultiplier
open Paper8NormalizedKloostermanRows Paper8EtaLevelZeroMode
open Paper8DedekindZeroReference (referenceZeroSum)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

noncomputable section

def actualZeroModeEntry {D : ℕ} (A : NormalizedRow D) : ℂ :=
  (starRingEnd ℂ) (principalEtaMultiplier A.1) *
    Complex.exp (periodCoefficient * (diagonalPhase A : ℂ))

theorem actualZeroModeEntry_eq {D : ℕ} (hD : 0 < D) (A : NormalizedRow D) :
    actualZeroModeEntry A = zeroModeEntry A := by
  unfold actualZeroModeEntry zeroModeEntry
  rw [principalEtaMultiplier_eq_dedekind A.1 A.2.1 hD]
  rfl

@[instance_reducible] def actualNormalizedFintype {D : ℕ} (hD : 0 < D) :
    Fintype (NormalizedRow D) :=
  Fintype.ofEquiv (ReducedResidue D) (rowsEquiv hD).symm

def actualLevelSum (N : ℕ) {D : ℕ} (hD : 0 < D) : ℂ := by
  classical
  letI := actualNormalizedFintype hD
  exact ∑ A : NormalizedRow D,
    if A.1 ∈ CongruenceSubgroup.Gamma0 N then actualZeroModeEntry A else 0

theorem actualLevelSum_eq (N : ℕ) {D : ℕ} (hD : 0 < D) :
    actualLevelSum N hD = levelSum N hD := by
  classical
  unfold actualLevelSum levelSum
  refine Fintype.sum_equiv (Equiv.refl (NormalizedRow D)) _ _ (fun A => ?_)
  simp only [Equiv.refl_apply, actualZeroModeEntry_eq hD]

theorem actualLevelSum_eq_reference (N : ℕ) {D : ℕ} (hD : 0 < D) :
    actualLevelSum N hD = if N ∣ D then etaPhase * referenceZeroSum D else 0 := by
  rw [actualLevelSum_eq, levelSum_eq]

theorem actualLevelTwo_sub_levelFour_eq_progression_two {D : ℕ} (hD : 0 < D) :
    actualLevelSum 2 hD - actualLevelSum 4 hD =
      if D % 4 = 2 then etaPhase * referenceZeroSum D else 0 := by
  rw [actualLevelSum_eq, actualLevelSum_eq, levelTwo_sub_levelFour_eq_progression_two]

end
end ManuscriptAudit.Paper8ActualEtaLevelSums

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaLevelSums.actualLevelSum_eq_reference,
      ``ManuscriptAudit.Paper8ActualEtaLevelSums.actualLevelTwo_sub_levelFour_eq_progression_two] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
