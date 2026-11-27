import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit

/-! The two-term product map for a sequential tower of additive commutative groups. -/

namespace ManuscriptAudit.InverseTowerDifference

universe u

noncomputable section

variable (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
variable (transition : ∀ n, G (n + 1) →+ G n)

/-- The consecutive coordinate difference on the product of the groups of a tower. -/
def difference : (∀ n, G n) →+ (∀ n, G n) where
  toFun x n := x n - transition n (x (n + 1))
  map_zero' := funext fun n ↦ by simp
  map_add' x y := funext fun n ↦ by
    change (x n + y n) - transition n (x (n + 1) + y (n + 1)) =
      (x n - transition n (x (n + 1))) + (y n - transition n (y (n + 1)))
    rw [map_add]
    abel

/-- The kernel of the product difference is the group of compatible tuples. -/
theorem ker_difference : (difference G transition).ker =
    CyclicPowerInverseLimit.compatibleTuples G transition := by
  ext x
  change difference G transition x = 0 ↔ ∀ n, transition n (x (n + 1)) = x n
  constructor
  · intro h n
    have hn : x n - transition n (x (n + 1)) = 0 := congrFun h n
    exact (sub_eq_zero.mp hn).symm
  · intro h
    funext n
    change x n - transition n (x (n + 1)) = 0
    rw [h n, sub_self]

variable (onto : ∀ n, Function.Surjective (transition n))

private def lift (y : ∀ n, G n) : ∀ n, G n
  | 0 => 0
  | n + 1 => Classical.choose (onto n (lift y n - y n))

/-- Surjective transitions make the consecutive difference map onto. -/
theorem difference_surjective : Function.Surjective (difference G transition) := by
  intro y
  refine ⟨lift G transition onto y, ?_⟩
  funext n
  have h : transition n (lift G transition onto y (n + 1)) =
      lift G transition onto y n - y n :=
    Classical.choose_spec (onto n (lift G transition onto y n - y n))
  change lift G transition onto y n - transition n (lift G transition onto y (n + 1)) = y n
  rw [h]
  abel

end
end ManuscriptAudit.InverseTowerDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.InverseTowerDifference.ker_difference,
      ``ManuscriptAudit.InverseTowerDifference.difference_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
