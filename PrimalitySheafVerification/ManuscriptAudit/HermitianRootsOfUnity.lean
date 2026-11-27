import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Scalar coordinates of finite roots-of-unity groups. -/

namespace ManuscriptAudit.HermitianRootsOfUnity

noncomputable section

def rootValue {K : Type*} [Field K] {m : ℕ} (z : rootsOfUnity m K) : K :=
  ((z : Kˣ) : K)

theorem rootValue_pow {K : Type*} [Field K] {m : ℕ} (z : rootsOfUnity m K) :
    rootValue z ^ m = 1 :=
  (mem_rootsOfUnity' m (z : Kˣ)).mp z.property

@[simp] theorem rootValue_mul {K : Type*} [Field K] {m : ℕ}
    (z w : rootsOfUnity m K) : rootValue (z * w) = rootValue z * rootValue w := rfl

theorem rootValue_ne_zero {K : Type*} [Field K] {m : ℕ} (z : rootsOfUnity m K) :
    rootValue z ≠ 0 := (z : Kˣ).ne_zero

theorem rootValue_injective {K : Type*} [Field K] (m : ℕ) :
    Function.Injective (rootValue : rootsOfUnity m K → K) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem pow_eq_one_of_order_dvd {K : Type*} [Field K] {m Q : ℕ} {z : K}
    (hz : z ^ m = 1) (h : m ∣ Q) : z ^ Q = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hz, one_pow]

end
end ManuscriptAudit.HermitianRootsOfUnity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianRootsOfUnity.rootValue_pow,
      ``ManuscriptAudit.HermitianRootsOfUnity.rootValue_injective,
      ``ManuscriptAudit.HermitianRootsOfUnity.pow_eq_one_of_order_dvd] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
