import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclotomicTraceAnnihilation
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Cubic conjugation on the point group gives trace zero on the native prime-adic limit. -/

namespace ManuscriptAudit.CyclotomicTateTrace

open PowerTateModule CyclotomicTraceAnnihilation

noncomputable section

variable (l : ℕ) [Fact l.Prime] {G : Type*} [AddCommGroup G]

theorem trace_eq_zero (S F : AddMonoid.End G)
    (hS : S ^ 3 = 1) (hQuad : S ^ 2 + S + 1 = 0)
    (hF : F * S = S ^ 2 * F) :
    LinearMap.trace ℤ_[l] (Tate l G) (endMap l F) = 0 := by
  apply trace_eq_zero_of_noZeroDivisors ℤ_[l] (Tate l G) (by norm_num) (endMap l S)
  · simpa only [map_pow, map_one] using congrArg (endMap l) hS
  · simpa only [map_add, map_pow, map_one, map_zero] using congrArg (endMap l) hQuad
  · simpa only [map_mul, map_pow] using congrArg (endMap l) hF

end
end ManuscriptAudit.CyclotomicTateTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CyclotomicTateTrace.trace_eq_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
