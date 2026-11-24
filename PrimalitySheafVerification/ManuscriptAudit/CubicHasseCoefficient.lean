import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Expand

/-!
# The Hasse coefficient in the printed cubic family

The characteristic-p fiber of the Paper 5 profile is (y^2=x^3+A).
The coefficient of (x^{p-1}) in ((x^3+A)^{(p-1)/2}) vanishes
when (pequiv2mod 3). The statements here compute this polynomial
coefficient. Its comparison with geometric Frobenius is a separate result.
-/

namespace ManuscriptAudit.CubicHasse

open Polynomial

theorem cubic_pow_coeff_eq_zero_of_not_dvd {R : Type*} [CommSemiring R]
    (a : R) (k n : ℕ) (hn : ¬ 3 ∣ n) :
    (((X : Polynomial R) ^ 3 + C a) ^ k).coeff n = 0 := by
  have h : ((X : Polynomial R) ^ 3 + C a) ^ k =
      expand R 3 (((X : Polynomial R) + C a) ^ k) := by
    simp only [map_pow, map_add, expand_X, expand_C]
  rw [h, coeff_expand (by decide : 0 < (3 : ℕ)), if_neg hn]

/-- The Hasse coefficient candidate is zero for each prime in the
residue class two modulo three, over its coefficient field. -/
theorem paper5_cubic_hasse_coefficient_zero {R : Type*} [CommSemiring R]
    (a : R) (p : ℕ) (hp : p % 3 = 2) :
    (((X : Polynomial R) ^ 3 + C a) ^ ((p - 1) / 2)).coeff (p - 1) = 0 := by
  apply cubic_pow_coeff_eq_zero_of_not_dvd
  rintro ⟨k, hk⟩
  omega

end ManuscriptAudit.CubicHasse

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHasse.cubic_pow_coeff_eq_zero_of_not_dvd,
      ``ManuscriptAudit.CubicHasse.paper5_cubic_hasse_coefficient_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
