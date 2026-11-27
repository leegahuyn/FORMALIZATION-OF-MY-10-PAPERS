import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! The rational coordinate inclusion underlying a relative power map has its literal degree. -/

namespace ManuscriptAudit.RationalPowerDegree

open Polynomial

/-- The field extension K(X)/K(X^n) has degree n, with finrank zero when n = 0. -/
theorem finrank_adjoin_power (K : Type*) [Field K] (n : ℕ) :
    Module.finrank
      (IntermediateField.adjoin K
        {algebraMap (Polynomial K) (RatFunc K) ((X : Polynomial K) ^ n)})
      (RatFunc K) = n := by
  rw [RatFunc.finrank_eq_max_natDegree]
  simp [Polynomial.natDegree_X_pow]

end ManuscriptAudit.RationalPowerDegree

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RationalPowerDegree.finrank_adjoin_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
