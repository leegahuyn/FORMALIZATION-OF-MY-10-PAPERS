import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! A compatible system of actual lifts of any specified m-torsion point. -/

namespace ManuscriptAudit.PowerTorsionLift

open PowerTorsionTower

noncomputable section

variable (m : ℕ) (G : Type*) [AddCommGroup G]

/-- Recursively lift a specified point along the native surjective transitions. -/
def lifted (h : Function.Surjective (fun P : G => m • P))
    (T : PowerTorsion m G 1) : (n : ℕ) → PowerTorsion m G (n + 1)
  | 0 => T
  | n + 1 => (transition_surjective m G h (n + 1) (lifted h T n)).choose

@[simp] theorem lifted_zero (h : Function.Surjective (fun P : G => m • P))
    (T : PowerTorsion m G 1) : lifted m G h T 0 = T := rfl

/-- The successive lifts agree under actual multiplication by m. -/
theorem transition_lifted (h : Function.Surjective (fun P : G => m • P))
    (T : PowerTorsion m G 1) (n : ℕ) :
    transition m G (n + 1) (lifted m G h T (n + 1)) = lifted m G h T n :=
  (transition_surjective m G h (n + 1) (lifted m G h T n)).choose_spec

/-- Each lift maps back to the given m-torsion point under multiplication by m^n. -/
theorem scale_lifted (h : Function.Surjective (fun P : G => m • P))
    (T : PowerTorsion m G 1) (n : ℕ) :
    (m ^ n : ℕ) • (lifted m G h T n : G) = (T : G) := by
  induction n with
  | zero => rw [lifted_zero, pow_zero, one_nsmul]
  | succ n ih =>
    have ht := congrArg (fun P : PowerTorsion m G (n + 1) => (P : G))
      (transition_lifted m G h T n)
    change m • (lifted m G h T (n + 1) : G) = (lifted m G h T n : G) at ht
    rw [pow_succ, mul_nsmul', ht, ih]

end
end ManuscriptAudit.PowerTorsionLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTorsionLift.transition_lifted,
      ``ManuscriptAudit.PowerTorsionLift.scale_lifted] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
