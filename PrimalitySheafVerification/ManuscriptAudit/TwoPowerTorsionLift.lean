import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionTower

/-! A compatible system of actual lifts of any specified two-torsion point. -/

namespace ManuscriptAudit.TwoPowerTorsionLift

open TwoPowerTorsionTower

noncomputable section

variable (G : Type*) [AddCommGroup G]

/-- Recursively lift a specified point along the native surjective transitions. -/
def lifted (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (T : PowerTorsion G 1) : (n : ℕ) → PowerTorsion G (n + 1)
  | 0 => T
  | n + 1 => (transition_surjective G h (n + 1) (lifted h T n)).choose

@[simp] theorem lifted_zero (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (T : PowerTorsion G 1) : lifted G h T 0 = T := rfl

/-- The successive lifts agree under actual doubling. -/
theorem transition_lifted (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (T : PowerTorsion G 1) (n : ℕ) :
    transition G (n + 1) (lifted G h T (n + 1)) = lifted G h T n :=
  (transition_surjective G h (n + 1) (lifted G h T n)).choose_spec

/-- Each lift maps back to the given order-two point under multiplication by 2^n. -/
theorem scale_lifted (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (T : PowerTorsion G 1) (n : ℕ) :
    (2 ^ n : ℕ) • (lifted G h T n : G) = (T : G) := by
  induction n with
  | zero => rw [lifted_zero, pow_zero, one_nsmul]
  | succ n ih =>
    have ht := congrArg (fun P : PowerTorsion G (n + 1) => (P : G))
      (transition_lifted G h T n)
    change (2 : ℕ) • (lifted G h T (n + 1) : G) = (lifted G h T n : G) at ht
    rw [pow_succ, mul_nsmul', ht, ih]

end
end ManuscriptAudit.TwoPowerTorsionLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTorsionLift.transition_lifted,
      ``ManuscriptAudit.TwoPowerTorsionLift.scale_lifted] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
