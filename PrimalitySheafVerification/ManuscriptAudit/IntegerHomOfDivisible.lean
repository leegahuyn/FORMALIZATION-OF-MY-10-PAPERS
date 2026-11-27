import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.NatAbs

/-! A divisible additive group has no nonzero image in the integers. -/

namespace ManuscriptAudit.IntegerHomOfDivisible

/-- Surjectivity of multiplication by every positive integer forces
any additive map into the integers to vanish. -/
theorem eq_zero {A : Type*} [AddCommGroup A] (f : A →+ ℤ)
    (h : ∀ n : ℕ, 0 < n → Function.Surjective (fun x : A ↦ n • x)) (x : A) :
    f x = 0 := by
  by_contra hx
  let n := (f x).natAbs + 1
  obtain ⟨y, hy⟩ := h n (Nat.succ_pos _) x
  have he : (f x).natAbs = n * (f y).natAbs := by
    rw [← hy, map_nsmul, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  have hdiv : n ∣ (f x).natAbs := ⟨_, he⟩
  have hp : 0 < (f x).natAbs :=
    Nat.pos_of_ne_zero fun hzero ↦ hx (Int.natAbs_eq_zero.mp hzero)
  exact Nat.not_succ_le_self _ (Nat.le_of_dvd hp hdiv)

end ManuscriptAudit.IntegerHomOfDivisible

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegerHomOfDivisible.eq_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
