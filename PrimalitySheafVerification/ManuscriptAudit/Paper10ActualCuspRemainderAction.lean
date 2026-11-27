import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombCuspEnergyIdentity
import PrimalitySheafVerification.ManuscriptAudit.Paper10RemainderOnCusp

/-! The quartic remainder obstructs the lower bound with the actual exterior cusp energy. -/

namespace ManuscriptAudit.Paper10ActualCuspRemainderAction

open LiteralCuspTruncation CoulombQuotientTestL2 CoulombNegativeQuotientForm
open CoulombCuspEnergyIdentity

noncomputable section

def rayAction (D : GammaTwoFundamentalDomain) (r t : ℝ) : ℝ :=
  t^2 * (exteriorEnergyOnQuotient D r / 2) + t^2 * massOnQuotient D r -
    (t^2 * massOnQuotient D r)^2

theorem ray_action_eq (D : GammaTwoFundamentalDomain) (r t : ℝ) (hr : 1 ≤ r)
    (hm : 0 < massOnQuotient D r) (ht : 0 ≤ t) :
    rayAction D r t = Paper10RemainderCoercivity.action
      ((exteriorEnergyOnQuotient D r / 2) / massOnQuotient D r) (t • testVector D r hr) := by
  have hs : ‖t • testVector D r hr‖^2 = t^2 * massOnQuotient D r := by
    rw [norm_smul, Real.norm_of_nonneg ht, mul_pow, testVector_norm_sq D r hr]
  have hq : ‖t • testVector D r hr‖^4 = (t^2 * massOnQuotient D r)^2 := by
    rw [show ‖t • testVector D r hr‖^4 = (‖t • testVector D r hr‖^2)^2 by ring, hs]
  unfold rayAction Paper10RemainderCoercivity.action Paper10RemainderCoercivity.leading
    Paper10RemainderCoercivity.mass Paper10RemainderCoercivity.remainder
  rw [hq, hs]
  field_simp [hm.ne'] <;> ring

theorem actual_exterior_energy_does_not_absorb_quartic (D : GammaTwoFundamentalDomain) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < massOnQuotient D r ∧
      ∀ B : ℝ, ∃ t : ℝ, 0 ≤ t ∧ rayAction D r t < B := by
  obtain ⟨r, hr, hm, _⟩ := negative_quotient_form_no_mass_lower_bound D 0
  have hv : testVector D r hr ≠ 0 := by
    intro h
    have hNorm := testVector_norm_sq D r hr
    rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hNorm
    exact hm.ne' hNorm.symm
  refine ⟨r, hr, hm, ?_⟩
  intro B
  obtain ⟨t, ht, hs⟩ := Paper10RemainderCoercivity.action_unbounded_on_every_nonzero_ray
    ((exteriorEnergyOnQuotient D r / 2) / massOnQuotient D r) hv B
  exact ⟨t, ht, (ray_action_eq D r t hr hm ht).trans_lt hs⟩

end
end ManuscriptAudit.Paper10ActualCuspRemainderAction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10ActualCuspRemainderAction.ray_action_eq,
      ``ManuscriptAudit.Paper10ActualCuspRemainderAction.actual_exterior_energy_does_not_absorb_quartic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
