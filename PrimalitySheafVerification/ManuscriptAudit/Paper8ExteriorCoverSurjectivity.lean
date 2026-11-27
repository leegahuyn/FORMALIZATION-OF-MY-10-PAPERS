import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorPrincipal

/-! The holomorphic root coordinate supplies a weighted value above every punctured-disk point. -/

namespace ManuscriptAudit.Paper8ExteriorCoverSurjectivity

open Paper8InsideComplexAnalytic Paper8ExteriorPrincipal Paper8ExteriorComplexHolomorphy

noncomputable section

theorem exists_lifted_normalized_exterior {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    ∃ w : ℂ, w ≠ 0 ∧ ‖w‖ < 1 ∧ w ^ (24 : ℕ) = q ∧
      normalizedCover w = w * standard q⁻¹ ∧
      Summable (fun n => ‖w * standardTerm n q⁻¹‖) := by
  let w := principalRoot q
  have hPower : w ^ (24 : ℕ) = q := principalRoot_pow q
  have hw₀ : w ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : (24 : ℕ) ≠ 0)] at hPower
    exact hq₀ hPower.symm
  have hw : ‖w‖ < 1 := by
    by_contra! h
    have hLe := pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) h (24 : ℕ)
    rw [← norm_pow, hPower, one_pow] at hLe
    exact (not_le_of_gt hq) hLe
  refine ⟨w, hw₀, hw, hPower, ?_, ?_⟩
  · rw [normalizedCover_eq_literal hw₀ hw, hPower]
  · simpa only [hPower] using normalizedCover_literal_absolute_summability hw₀ hw

end
end ManuscriptAudit.Paper8ExteriorCoverSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8ExteriorCoverSurjectivity.exists_lifted_normalized_exterior
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
