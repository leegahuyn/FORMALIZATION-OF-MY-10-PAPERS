import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite

/-! A map to a finite type with at most two points in each fiber bounds the source cardinality. -/

namespace ManuscriptAudit.TwoPointFiberCard

noncomputable section

variable {X Y : Type*} [Finite Y]

/-- A finite target with fibers containing no three distinct elements gives the size bound. -/
theorem card_le_two_mul (f : X → Y)
    (h : ∀ x y z : X, f x = f y → f x = f z → x = y ∨ x = z ∨ y = z) :
    Nat.card X ≤ 2 * Nat.card Y := by
  classical
  let j (x : X) : Set.range f := ⟨f x, x, rfl⟩
  let s (y : Set.range f) : X := Classical.choose y.property
  have hs (y : Set.range f) : f (s y) = y.val := Classical.choose_spec y.property
  let e (x : X) : Y × Bool := (f x, decide (x = s (j x)))
  have he : Function.Injective e := by
    intro x y hxy
    have hf : f x = f y := congrArg Prod.fst hxy
    have hj : j x = j y := Subtype.ext hf
    have hb : decide (x = s (j x)) = decide (y = s (j x)) := by
      have hb : decide (x = s (j x)) = decide (y = s (j y)) := congrArg Prod.snd hxy
      simpa only [← hj] using hb
    by_cases hx : x = s (j x)
    · have ht : decide (x = s (j x)) = true := decide_eq_true hx
      have hy : y = s (j x) := of_decide_eq_true (hb.symm.trans ht)
      exact hx.trans hy.symm
    · rcases h x y (s (j x)) hf (hs (j x)).symm with hxy | hx' | hy
      · exact hxy
      · exact (hx hx').elim
      · have ht : decide (y = s (j x)) = true := decide_eq_true hy
        exact (hx (of_decide_eq_true (hb.trans ht))).elim
  calc
    Nat.card X ≤ Nat.card (Y × Bool) := Nat.card_le_card_of_injective e he
    _ = 2 * Nat.card Y := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
      Fintype.card_bool, Nat.mul_comm]

end

end ManuscriptAudit.TwoPointFiberCard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoPointFiberCard.card_le_two_mul
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
