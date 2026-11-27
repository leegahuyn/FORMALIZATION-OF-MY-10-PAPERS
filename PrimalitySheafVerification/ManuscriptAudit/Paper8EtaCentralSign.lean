import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation

/-! The mod-four character's central sign in the actual level-four group. -/

namespace ManuscriptAudit.Paper8EtaCentralSign

open Matrix UpperHalfPlane
open Paper8OddCrossCuspRows Paper8OddCrossCuspCutoff Paper8DedekindZeroReference
open Paper8ContourResidueWeights (dedekindSum sawtooth)
open scoped MatrixGroups

def centralNeg (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨-1, by
    have hEntry : ((-1 : SL(2, ℤ)) 1 0) = 0 := by
      change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = 0
      simp [Matrix.one_apply]
    rw [CongruenceSubgroup.Gamma0_mem, hEntry]
    simp⟩

theorem centralNeg_smul (N : ℕ) (z : ℍ) : (centralNeg N : SL(2, ℤ)) • z = z := by
  change (-1 : SL(2, ℤ)) • z = z
  simp

theorem levelCharacter_centralNeg : levelCharacter (centralNeg 4) = -1 := by
  rw [levelCharacter_apply]
  have hEntry : ((centralNeg 4 : SL(2, ℤ)) 1 1) = -1 := by
    change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 = -1
    simp [Matrix.one_apply]
  rw [hEntry]
  decide

/-- A relative twist of eta by this character at unchanged weight has no sections.
This uses the actual level-four central element, independently of cusp conditions. -/
theorem unchanged_weight_section_eq_zero (F : ℍ → ℂ)
    (h : ∀ (g : CongruenceSubgroup.Gamma0 4) (z : ℍ),
      F ((g : SL(2, ℤ)) • z) * ModularForm.eta z =
        (levelCharacter g : ℂ) * (F z * ModularForm.eta ((g : SL(2, ℤ)) • z : ℍ))) :
    F = 0 := by
  funext z
  have hz := h (centralNeg 4) z
  rw [centralNeg_smul, levelCharacter_centralNeg, Int.cast_neg, Int.cast_one, neg_one_mul] at hz
  have hProd : F z * ModularForm.eta z = 0 := by linear_combination hz / 2
  exact (mul_eq_zero.mp hProd).resolve_right (ModularForm.eta_ne_zero z.im_pos)

/-- The positive-modulus weighted finite sum does not vanish identically.
Its nonzero value here distinguishes it from the unchanged-weight space. -/
theorem first_cross_sum : crossSum (D := 1) (by decide) = 1 := by
  rw [crossSum_eq]
  have hS : dedekindSum 0 1 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_one, sawtooth]
  unfold referenceZeroSum
  rw [Finset.sum_filter, Fin.sum_univ_one]
  norm_num [chiFour, hS]

end ManuscriptAudit.Paper8EtaCentralSign

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaCentralSign.centralNeg_smul,
      ``ManuscriptAudit.Paper8EtaCentralSign.levelCharacter_centralNeg,
      ``ManuscriptAudit.Paper8EtaCentralSign.unchanged_weight_section_eq_zero,
      ``ManuscriptAudit.Paper8EtaCentralSign.first_cross_sum] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
