import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspNormalization
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProgressionSqrtMainTerm

/-!
# Exact finite cross-cusp attachment of the odd progression difference

The sum is over the normalized integral cross-cusp matrices. Its
explicit weights use the transported eta phase and the mod-four
character of the lower right entry of the level matrix. In the
scaled convention the modulus is 2D, while this cutoff divides by D.
-/

namespace ManuscriptAudit.Paper8OddCrossCuspCutoff

open Paper8NormalizedKloostermanRows Paper8OddCrossCuspRows
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspPhase
open Paper8EtaLevelZeroMode (referenceEntry)
open Paper8DedekindZeroReference (referenceZeroSum reducedFrequencySum_zero_eq_conj)
open Paper8UnshiftedZeroMode (rawTerm)
open Paper8ProgressionSqrtMainTerm (zeroModeProgressionRaw)

noncomputable section

private theorem character_mod (D : ℕ) :
    chiFour (D : ZMod 4) =
      if D % 4 = 1 then 1 else if D % 4 = 3 then -1 else 0 := by
  have h1 : ((D : ZMod 4) = 1) ↔ D % 4 = 1 := by
    simpa using ZMod.natCast_eq_natCast_iff' D 1 4
  have h3 : ((D : ZMod 4) = 3) ↔ D % 4 = 3 := by
    simpa using ZMod.natCast_eq_natCast_iff' D 3 4
  simp only [chiFour, h1, h3]

@[instance_reducible] private noncomputable def rowFintype {D : ℕ} (hD : 0 < D) :
    Fintype (NormalizedRow D) :=
  Fintype.ofEquiv (ReducedResidue D) (rowsEquiv hD).symm

@[instance_reducible] private noncomputable def crossFintype {D : ℕ} (hD : 0 < D) (hOdd : Odd D) :
    Fintype (CrossRow D) :=
  letI := rowFintype hD
  Fintype.ofEquiv (NormalizedRow D) (crossRowsEquiv hD hOdd)

def crossSum {D : ℕ} (hD : 0 < D) : ℂ := by
  classical
  exact if hOdd : Odd D then
    letI := crossFintype hD hOdd
    ∑ A : CrossRow D, crossEntry D (A.matrix 0 0) (A.matrix 1 1)
  else 0

private theorem referenceZeroSum_subtype (D : ℕ) :
    referenceZeroSum D =
      ∑ d : ReducedResidue D, referenceEntry D (d.1.val : ℤ) := by
  unfold referenceZeroSum
  exact Finset.sum_subtype _ (fun d => by simp) _

theorem crossSum_eq {D : ℕ} (hD : 0 < D) :
    crossSum hD = (chiFour (D : ZMod 4) : ℂ) * referenceZeroSum D := by
  classical
  letI := rowFintype hD
  by_cases hOdd : Odd D
  · unfold crossSum
    rw [dif_pos hOdd]
    letI := crossFintype hD hOdd
    let f := fun A : CrossRow D => crossEntry D (A.matrix 0 0) (A.matrix 1 1)
    let g := fun A : NormalizedRow D =>
      (chiFour (D : ZMod 4) : ℂ) * referenceEntry D (A.1 1 1)
    calc
      _ = ∑ A : NormalizedRow D, g A := by
        symm
        refine Fintype.sum_equiv (crossRowsEquiv hD hOdd) g f (fun A => ?_)
        let m : ℤ := (chosenShift hOdd A).val
        have hEntries := rightTranslation_entries A.1 m
        change (chiFour (D : ZMod 4) : ℂ) * referenceEntry D (A.1 1 1) =
          crossEntry D ((A.1 * ModularGroup.T ^ m) 0 0) ((A.1 * ModularGroup.T ^ m) 1 1)
        rw [hEntries.1, hEntries.2.2, A.property.1, translated_crossEntry_eq hD]
      _ = ∑ d : ReducedResidue D,
          (chiFour (D : ZMod 4) : ℂ) * referenceEntry D (d.1.val : ℤ) := by
        refine Fintype.sum_equiv (rowsEquiv hD) _ _ (fun A => ?_)
        unfold g
        rw [rowsEquiv_bottom_cast hD A]
      _ = _ := by rw [referenceZeroSum_subtype, Finset.mul_sum]
  · unfold crossSum
    rw [dif_neg hOdd]
    have hEven : D % 2 = 0 := by
      have hh : D % 2 ≠ 1 := fun h => hOdd (Nat.odd_iff.mpr h)
      omega
    have h1 : D % 4 ≠ 1 := by omega
    have h3 : D % 4 ≠ 3 := by omega
    simp [character_mod, h1, h3]

def crossRaw (j : ℕ) : ℂ :=
  crossSum (Nat.succ_pos j) / ((j + 1 : ℕ) : ℂ)

theorem crossRaw_oddProgressionDifference (j : ℕ) :
    crossRaw j = (starRingEnd ℂ) (zeroModeProgressionRaw 1 j - zeroModeProgressionRaw 3 j) := by
  have hRaw : (starRingEnd ℂ) (rawTerm j) = referenceZeroSum (j + 1) / ((j + 1 : ℕ) : ℂ) := by
    rw [rawTerm, reducedFrequencySum_zero_eq_conj, map_div₀]
    simp
  unfold crossRaw zeroModeProgressionRaw
  rw [crossSum_eq, character_mod]
  by_cases h1 : (j + 1) % 4 = 1
  · simp [h1, hRaw]
  · by_cases h3 : (j + 1) % 4 = 3
    · simp [h3, hRaw, neg_div]
    · simp [h1, h3]

theorem crossCutoff_oddProgressionDifference (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), crossRaw j) =
      (starRingEnd ℂ) ((∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw 1 j) -
        ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw 3 j) := by
  rw [← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_congr rfl (fun j _ => crossRaw_oddProgressionDifference j)

end
end ManuscriptAudit.Paper8OddCrossCuspCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossCuspCutoff.crossSum_eq,
      ``ManuscriptAudit.Paper8OddCrossCuspCutoff.crossRaw_oddProgressionDifference,
      ``ManuscriptAudit.Paper8OddCrossCuspCutoff.crossCutoff_oddProgressionDifference] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
