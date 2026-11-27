import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10RemainderCoercivity
import PrimalitySheafVerification.ManuscriptAudit.CoulombQuotientTestL2

/-! The remainder obstruction can be placed on a nonzero compact cusp test in the actual quotient. -/

namespace ManuscriptAudit.Paper10RemainderOnCusp

open LiteralCuspTruncation CoulombQuotientTestL2 CoulombNegativeQuotientForm
open Paper10RemainderCoercivity

theorem actual_cusp_ray_unbounded (D : GammaTwoFundamentalDomain) (a : ℝ) :
    ∃ (r : ℝ) (hr : 1 ≤ r), testVector D r hr ≠ 0 ∧
      ∀ B : ℝ, ∃ t : ℝ, 0 ≤ t ∧ action a (t • testVector D r hr) < B := by
  obtain ⟨r,hr,hm,_⟩ := negative_quotient_form_no_mass_lower_bound D 0
  have hv : testVector D r hr ≠ 0 := by
    intro h
    have hNorm := testVector_norm_sq D r hr
    rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hNorm
    exact hm.ne' hNorm.symm
  exact ⟨r,hr,hv,action_unbounded_on_every_nonzero_ray a hv⟩

end ManuscriptAudit.Paper10RemainderOnCusp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper10RemainderOnCusp.actual_cusp_ray_unbounded
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
