import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaDedekindTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspNormalization
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCuspWidths
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode

/-! Canonical representatives for the two cusp translation actions in the actual odd cross sum. -/

namespace ManuscriptAudit.Paper8OddCrossDoubleCosets

open Matrix Paper8EtaDedekindTranslation Paper8OddCrossCuspNormalization Paper8EtaCuspWidths
open Paper8EtaLevelZeroMode (translation_mem_level)
open scoped MatrixGroups

noncomputable section

def crossShift (g : SL(2, ℤ)) (m n : ℤ) : SL(2, ℤ) :=
  ModularGroup.T ^ m * g * ModularGroup.T ^ (4 * n)

private theorem left_T_entries (g : SL(2, ℤ)) (m : ℤ) :
    (ModularGroup.T ^ m * g) 0 0 = g 0 0 + m * g 1 0 ∧
    (ModularGroup.T ^ m * g) 1 0 = g 1 0 ∧
    (ModularGroup.T ^ m * g) 1 1 = g 1 1 := by
  change ((ModularGroup.T ^ m).1 * g.1) 0 0 = g 0 0 + m * g 1 0 ∧
    ((ModularGroup.T ^ m).1 * g.1) 1 0 = g 1 0 ∧ ((ModularGroup.T ^ m).1 * g.1) 1 1 = g 1 1
  rw [ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem crossShift_entries (g : SL(2, ℤ)) (m n : ℤ) :
    crossShift g m n 0 0 = g 0 0 + m * g 1 0 ∧
    crossShift g m n 1 0 = g 1 0 ∧
    crossShift g m n 1 1 = g 1 1 + g 1 0 * (4 * n) := by
  obtain ⟨ha, hc, hd⟩ := left_T_entries g m
  obtain ⟨ha', hc', hd'⟩ := right_T_entries (ModularGroup.T ^ m * g) (4 * n)
  exact ⟨ha'.trans ha, hc'.trans hc, hd'.trans (by rw [hd, hc])⟩

theorem crossShift_atLevel {g : SL(2, ℤ)}
    (hLevel : g * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4) (m n : ℤ) :
    crossShift g m n * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4 := by
  let H := CongruenceSubgroup.Gamma0 4
  have hL : (ModularGroup.T ^ m : SL(2, ℤ)) ∈ H := H.zpow_mem (translation_mem_level 4) m
  have hR : ModularGroup.S * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹ ∈ H := by
    apply (conjugatedTranslation_mem_iff 4 ModularGroup.S (4 * n)).2
    refine ⟨ModularGroup.S 1 0 ^ 2 * n, ?_⟩
    ring
  have hP := H.mul_mem (H.mul_mem hL hLevel) hR
  have hM : (ModularGroup.T ^ m * (g * ModularGroup.S⁻¹)) *
      (ModularGroup.S * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹) =
      crossShift g m n * ModularGroup.S⁻¹ := by
    unfold crossShift
    simp only [mul_assoc, inv_mul_cancel_left]
  rwa [hM] at hP

def normalizeCrossRow {D : ℕ} (hD : 0 < D) (g : SL(2, ℤ)) (hC : g 1 0 = (D : ℤ))
    (hLevel : g * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma0 4) : CrossRow D := by
  let c : ℤ := D
  let m : ℤ := -(g 0 0 / c)
  let n : ℤ := -(g 1 1 / (4 * c))
  have hc : 0 < c := by dsimp only [c]; exact_mod_cast hD
  have hc4 : 0 < 4 * c := by positivity
  obtain ⟨ha, hc', hd⟩ := crossShift_entries g m n
  have hA : crossShift g m n 0 0 = g 0 0 % c := by
    rw [ha, hC, Int.emod_def]
    dsimp only [m, c]
    ring
  have hB : crossShift g m n 1 1 = g 1 1 % (4 * c) := by
    rw [hd, hC, Int.emod_def]
    dsimp only [n, c]
    ring
  refine ⟨crossShift g m n, hc'.trans hC, ?_, ?_, ?_, ?_, crossShift_atLevel hLevel m n⟩
  · rw [hA]
    exact Int.emod_nonneg _ hc.ne'
  · rw [hA]
    exact Int.emod_lt_of_pos _ hc
  · rw [hB]
    exact Int.emod_nonneg _ hc4.ne'
  · rw [hB]
    exact Int.emod_lt_of_pos _ hc4

theorem normalizedCross_shift_unique {D : ℕ} (hD : 0 < D) (A B : CrossRow D) (m n : ℤ)
    (h : crossShift A.matrix m n = B.matrix) : m = 0 ∧ n = 0 ∧ A = B := by
  let c : ℤ := D
  have hc : 0 < c := by dsimp only [c]; exact_mod_cast hD
  obtain ⟨ha, _, hd⟩ := crossShift_entries A.matrix m n
  rw [h, A.lowerLeft] at ha hd
  have hA : B.matrix 0 0 = A.matrix 0 0 := by
    calc
      _ = B.matrix 0 0 % c := (Int.emod_eq_of_lt B.topNonneg B.topBound).symm
      _ = A.matrix 0 0 % c := by
        rw [ha]
        change (A.matrix 0 0 + m * c) % c = _
        simp
      _ = _ := Int.emod_eq_of_lt A.topNonneg A.topBound
  have hB : B.matrix 1 1 = A.matrix 1 1 := by
    calc
      _ = B.matrix 1 1 % (4 * c) := (Int.emod_eq_of_lt B.bottomNonneg B.bottomBound).symm
      _ = A.matrix 1 1 % (4 * c) := by
        rw [hd]
        have hP : c * (4 * n) = n * (4 * c) := by ring
        change (A.matrix 1 1 + c * (4 * n)) % (4 * c) = _
        rw [hP]
        simp
      _ = _ := Int.emod_eq_of_lt A.bottomNonneg A.bottomBound
  have hm0 : m * c = 0 := by change B.matrix 0 0 = A.matrix 0 0 + m * c at ha; omega
  have hn0 : c * (4 * n) = 0 := by change B.matrix 1 1 = A.matrix 1 1 + c * (4 * n) at hd; omega
  have hm : m = 0 := (mul_eq_zero.mp hm0).resolve_right hc.ne'
  have hn : n = 0 := by
    have h₀ := (mul_eq_zero.mp hn0).resolve_left hc.ne'
    omega
  refine ⟨hm, hn, ?_⟩
  apply CrossRow.ext
  simpa only [crossShift, hm, hn, mul_zero, zpow_zero, one_mul, mul_one] using h

end
end ManuscriptAudit.Paper8OddCrossDoubleCosets

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossDoubleCosets.normalizeCrossRow,
      ``ManuscriptAudit.Paper8OddCrossDoubleCosets.normalizedCross_shift_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
