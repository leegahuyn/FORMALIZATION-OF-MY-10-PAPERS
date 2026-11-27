import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RationalPowerHeight

/-! Rational substitution by the original coordinate is literally the identity. -/

namespace ManuscriptAudit.RationalIdentityHeight

open Polynomial RationalSubstitutionDegree RationalPowerHeight

variable {K : Type*} [Field K]

theorem degree_constant (c : K) : rationalDegree (RatFunc.C c) = 0 := by
  simp [rationalDegree]

theorem nonconstant_of_degree_pos {r : RatFunc K} (h : 0 < rationalDegree r) :
    ¬ ∃ c : K, r = RatFunc.C c := by
  rintro ⟨c, rfl⟩
  rw [degree_constant] at h
  exact Nat.lt_irrefl 0 h

theorem X_nonconstant : ¬ ∃ c : K, (RatFunc.X : RatFunc K) = RatFunc.C c := by
  apply nonconstant_of_degree_pos
  have hh : rationalDegree (RatFunc.X : RatFunc K) = 1 := by
    simpa only [pow_one] using (degree_X_pow (K := K) 1)
  rw [hh]
  exact Nat.zero_lt_succ 0

/-- Substitution by the generator of K(X) acts identically on all rational functions. -/
theorem substitute_identity (r : RatFunc K) :
    substitute RatFunc.X (X_nonconstant (K := K)) r = r := by
  let s := substitute RatFunc.X (X_nonconstant (K := K))
  have h (p : Polynomial K) : s (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p := by
    change (substitute RatFunc.X (X_nonconstant (K := K))) (algebraMap K[X] (RatFunc K) p) = _
    rw [substitute_algebraMap]
    let e := IsScalarTower.toAlgHom K K[X] (RatFunc K)
    change aeval (e X) p = e p
    rw [aeval_algHom_apply, aeval_X_left, AlgHom.id_apply]
  change s r = r
  calc
    s r = s (algebraMap K[X] (RatFunc K) r.num / algebraMap K[X] (RatFunc K) r.denom) :=
      congrArg s r.num_div_denom.symm
    _ = r := by rw [map_div₀, h, h, RatFunc.num_div_denom]

end ManuscriptAudit.RationalIdentityHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RationalIdentityHeight.degree_constant,
      ``ManuscriptAudit.RationalIdentityHeight.X_nonconstant,
      ``ManuscriptAudit.RationalIdentityHeight.substitute_identity] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
