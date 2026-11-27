import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.Nat.Find

/-!
# Cusp translation widths for the native group Γ₀(N)

A cusp representative g carries infinity to the cusp. The positive
translation width is the least m with g T^m g⁻¹ in Γ₀(N).
The lower left entry gives its exact divisibility criterion and
bounds all cusp widths by N.
-/

namespace ManuscriptAudit.Paper8EtaCuspWidths

open Matrix
open scoped MatrixGroups

theorem conjugatedTranslation_lowerLeft (g : SL(2, ℤ)) (m : ℤ) :
    (g * ModularGroup.T ^ m * g⁻¹) 1 0 = -(g 1 0 ^ 2 * m) := by
  change ((g.1 * (ModularGroup.T ^ m).1) * (g⁻¹).1) 1 0 = _
  rw [ModularGroup.coe_T_zpow, SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem conjugatedTranslation_mem_iff (N : ℕ) (g : SL(2, ℤ)) (m : ℤ) :
    g * ModularGroup.T ^ m * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ g 1 0 ^ 2 * m := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd,
    conjugatedTranslation_lowerLeft, dvd_neg]

theorem conjugatedTranslation_level (N : ℕ) (g : SL(2, ℤ)) :
    g * ModularGroup.T ^ (N : ℤ) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [conjugatedTranslation_mem_iff, mul_comm]
  exact dvd_mul_right _ _

noncomputable def cuspWidth {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) : ℕ := by
  classical
  exact Nat.find (show ∃ m : ℕ, 0 < m ∧
      g * ModularGroup.T ^ (m : ℤ) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N from
    ⟨N, hN, conjugatedTranslation_level N g⟩)

theorem cuspWidth_positive_mem {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) :
    0 < cuspWidth hN g ∧ g * ModularGroup.T ^ (cuspWidth hN g : ℤ) * g⁻¹
      ∈ CongruenceSubgroup.Gamma0 N := by
  classical
  unfold cuspWidth
  exact Nat.find_spec _

theorem cuspWidth_le_level {N : ℕ} (hN : 0 < N) (g : SL(2, ℤ)) :
    cuspWidth hN g ≤ N := by
  classical
  unfold cuspWidth
  exact Nat.find_min' _ ⟨hN, conjugatedTranslation_level N g⟩

theorem halfWeightEta_cuspOrder_bounds {N : ℕ} (hN : 0 < N) (hN24 : N < 24)
    (g : SL(2, ℤ)) :
    (0 : ℝ) < (cuspWidth hN g : ℝ) / 24 ∧ (cuspWidth hN g : ℝ) / 24 < 1 := by
  have hLower : (0 : ℝ) < (cuspWidth hN g : ℝ) := by
    exact_mod_cast (cuspWidth_positive_mem hN g).1
  have hUpper : (cuspWidth hN g : ℝ) < 24 := by
    exact_mod_cast (cuspWidth_le_level hN g).trans_lt hN24
  constructor
  · positivity
  · change (cuspWidth hN g : ℝ) / 24 < (1 : ℝ)
    rw [div_lt_iff₀ (by norm_num), one_mul]
    exact hUpper

end ManuscriptAudit.Paper8EtaCuspWidths

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaCuspWidths.conjugatedTranslation_lowerLeft,
      ``ManuscriptAudit.Paper8EtaCuspWidths.conjugatedTranslation_mem_iff,
      ``ManuscriptAudit.Paper8EtaCuspWidths.cuspWidth_positive_mem,
      ``ManuscriptAudit.Paper8EtaCuspWidths.cuspWidth_le_level,
      ``ManuscriptAudit.Paper8EtaCuspWidths.halfWeightEta_cuspOrder_bounds] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
