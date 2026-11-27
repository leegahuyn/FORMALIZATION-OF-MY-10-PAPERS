import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCuspWidths
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddReducedLevelEightRows

/-! Exact scaling widths and trivial character on the needed cusp translations. -/

namespace ManuscriptAudit.Paper8CrossCuspScalingWidths

open Matrix Paper8EtaCuspWidths Paper8OddCrossCuspRows Paper8OddReducedLevelEightRows
open scoped MatrixGroups

private theorem width_le_candidate {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) {m : ℕ} (hm : 0 < m)
    (h : g * ModularGroup.T ^ (m : ℤ) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N) :
    cuspWidth hN g ≤ m := by
  classical
  unfold cuspWidth
  exact Nat.find_min' (p := fun q : ℕ => 0 < q ∧
    g * ModularGroup.T ^ (q : ℤ) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    ⟨N, hN, conjugatedTranslation_level N g⟩ ⟨hm, h⟩

theorem width_zero_levelFour : cuspWidth (N := 4) (by decide) ModularGroup.S = 4 := by
  have hSpec := cuspWidth_positive_mem (N := 4) (by decide) ModularGroup.S
  have hDvd := (conjugatedTranslation_mem_iff 4 ModularGroup.S _).1 hSpec.2
  have hDvd' : (4 : ℤ) ∣ (cuspWidth (N := 4) (by decide) ModularGroup.S : ℤ) := by
    simpa [ModularGroup.coe_S] using hDvd
  have hDvd'' : 4 ∣ cuspWidth (N := 4) (by decide) ModularGroup.S := by exact_mod_cast hDvd'
  exact le_antisymm (cuspWidth_le_level (N := 4) (by decide) _) (Nat.le_of_dvd hSpec.1 hDvd'')

theorem width_half_levelEight : cuspWidth (N := 8) (by decide) halfCuspMatrix = 2 := by
  have hTwo : halfCuspMatrix * ModularGroup.T ^ (2 : ℤ) * halfCuspMatrix⁻¹ ∈
      CongruenceSubgroup.Gamma0 8 := by
    apply (conjugatedTranslation_mem_iff 8 halfCuspMatrix _).2
    change (8 : ℤ) ∣ (2 : ℤ) ^ 2 * 2
    decide
  have hLe : cuspWidth (N := 8) (by decide) halfCuspMatrix ≤ 2 :=
    width_le_candidate (N := 8) (by decide) halfCuspMatrix (by decide) hTwo
  have hSpec := cuspWidth_positive_mem (N := 8) (by decide) halfCuspMatrix
  have hDvd := (conjugatedTranslation_mem_iff 8 halfCuspMatrix _).1 hSpec.2
  change (8 : ℤ) ∣ 2 ^ 2 * (cuspWidth (N := 8) (by decide) halfCuspMatrix : ℤ) at hDvd
  norm_num at hDvd
  omega

private theorem translation_lowerRight (g : SL(2, ℤ)) (m : ℤ) :
    (g * ModularGroup.T ^ m * g⁻¹) 1 1 = 1 + g 0 0 * g 1 0 * m := by
  have hDet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  change ((g.1 * (ModularGroup.T ^ m).1) * (g⁻¹).1) 1 1 = _
  rw [ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hDet

theorem character_zero_translation (m : ℤ) :
    chiFour (((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹) 1 1 : ℤ) : ZMod 4) = 1 := by
  rw [translation_lowerRight]
  have hS : ModularGroup.S 0 0 = 0 := rfl
  rw [hS, zero_mul, zero_mul, add_zero] <;> decide

theorem character_half_translation :
    chiFour (((halfCuspMatrix * ModularGroup.T ^ (2 : ℤ) * halfCuspMatrix⁻¹) 1 1 : ℤ) : ZMod 4) =
      1 := by
  rw [translation_lowerRight]
  change chiFour (((1 + (1 : ℤ) * 2 * 2 : ℤ) : ZMod 4)) = 1
  decide

end ManuscriptAudit.Paper8CrossCuspScalingWidths

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CrossCuspScalingWidths.width_zero_levelFour,
      ``ManuscriptAudit.Paper8CrossCuspScalingWidths.width_half_levelEight,
      ``ManuscriptAudit.Paper8CrossCuspScalingWidths.character_zero_translation,
      ``ManuscriptAudit.Paper8CrossCuspScalingWidths.character_half_translation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
