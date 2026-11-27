import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic.Abel

/-! The sequential product difference has the expected kernel and is onto for onto transitions. -/

namespace ManuscriptAudit.SequentialInverseLimitDifference

noncomputable section

variable (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
variable (transition : ∀ n, A (n + 1) →+ A n)

def productDifference : ((n : ℕ) → A n) →+ ((n : ℕ) → A n) where
  toFun x n := x n - transition n (x (n + 1))
  map_zero' := funext fun n => by
    change (0 : A n) - transition n 0 = 0
    rw [map_zero, sub_zero]
  map_add' x y := funext fun n => by
    change x n + y n - transition n (x (n + 1) + y (n + 1)) =
      (x n - transition n (x (n + 1))) + (y n - transition n (y (n + 1)))
    rw [map_add]
    abel

theorem productDifference_eq_zero_iff (x : (n : ℕ) → A n) :
    productDifference A transition x = 0 ↔ ∀ n, transition n (x (n + 1)) = x n := by
  constructor
  · intro h n
    exact (sub_eq_zero.mp (congrFun h n)).symm
  · intro h
    funext n
    exact sub_eq_zero.mpr (h n).symm

theorem productDifference_surjective (hSurj : ∀ n, Function.Surjective (transition n)) :
    Function.Surjective (productDifference A transition) := by
  intro b
  let x : (n : ℕ) → A n :=
    Nat.rec (motive := A) 0 (fun n v => (hSurj n (v - b n)).choose)
  have hn (n : ℕ) : transition n (x (n + 1)) = x n - b n :=
    (hSurj n (x n - b n)).choose_spec
  refine ⟨x, funext fun n => ?_⟩
  change x n - transition n (x (n + 1)) = b n
  rw [hn]
  abel

end
end ManuscriptAudit.SequentialInverseLimitDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SequentialInverseLimitDifference.productDifference_eq_zero_iff,
      ``ManuscriptAudit.SequentialInverseLimitDifference.productDifference_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
