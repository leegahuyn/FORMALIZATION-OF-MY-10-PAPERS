import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RationalSubstitutionDegree

/-! Normalized one-variable rational degree scales by the exponent under powers. -/

namespace ManuscriptAudit.RationalPowerHeight

open Polynomial RationalSubstitutionDegree

variable {K : Type*} [Field K]

theorem degree_X_pow (n : ℕ) : rationalDegree ((RatFunc.X : RatFunc K) ^ n) = n := by
  rw [rationalDegree, ← RatFunc.algebraMap_X, ← map_pow, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap, natDegree_X_pow, natDegree_one]
  simp

theorem degree_pow (r : RatFunc K) (n : ℕ) :
    rationalDegree (r ^ n) = n * rationalDegree r := by
  by_cases hr : ∃ c : K, r = RatFunc.C c
  · obtain ⟨c, rfl⟩ := hr
    have hconst (c : K) : rationalDegree (RatFunc.C c) = 0 := by
      rw [rationalDegree, ← RatFunc.algebraMap_C, RatFunc.num_algebraMap,
        RatFunc.denom_algebraMap, natDegree_C, natDegree_one]
      rfl
    rw [← map_pow, hconst, hconst, mul_zero]
  · have h := rationalDegree_substitute ((RatFunc.X : RatFunc K) ^ n) r hr
    rw [map_pow, substitute_X, degree_X_pow] at h
    exact h

end ManuscriptAudit.RationalPowerHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RationalPowerHeight.degree_X_pow,
      ``ManuscriptAudit.RationalPowerHeight.degree_pow] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
