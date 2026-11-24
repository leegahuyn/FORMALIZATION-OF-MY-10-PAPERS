import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision

/-!
The punctured cusp normalization has a Laurent polynomial coordinate ring.
This file identifies its units and gives an explicit nontrivial class
for the quotient of those units by d-th powers, for d at least two.
-/

namespace ManuscriptAudit.LaurentUnits

open LaurentPolynomial

variable (K : Type*) [Field K]

/-- Every Laurent polynomial unit is a single monomial with unit coefficient. -/
theorem laurent_isUnit_iff_monomial (f : LaurentPolynomial K) :
    IsUnit f ↔ ∃ (c : K) (n : ℤ), IsUnit c ∧ f = C c * T n := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨m, p, hp⟩ := exists_T_pow (u : LaurentPolynomial K)
    obtain ⟨n, q, hq⟩ := exists_T_pow (↑(u⁻¹) : LaurentPolynomial K)
    have hpq : p * q = (Polynomial.X : Polynomial K) ^ (m + n) := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow, Nat.cast_add, T_add]
      calc
        _ = ((u : LaurentPolynomial K) * ↑(u⁻¹)) * (T (m : ℤ) * T (n : ℤ)) := by ac_rfl
        _ = _ := by rw [Units.mul_inv, one_mul]
    obtain ⟨i, _, hi⟩ := (dvd_prime_pow (Polynomial.prime_X (R := K)) (m + n)).mp ⟨q, hpq.symm⟩
    obtain ⟨v, hv⟩ := hi.symm
    obtain ⟨c, hc, hconst⟩ := Polynomial.isUnit_iff.mp v.isUnit
    have hpmon : p = Polynomial.C c * Polynomial.X ^ i := by
      calc
        p = (Polynomial.X : Polynomial K) ^ i * (v : Polynomial K) := hv.symm
        _ = Polynomial.C c * Polynomial.X ^ i := by rw [← hconst, mul_comm]
    refine ⟨c, (i : ℤ) - m, hc, ?_⟩
    calc
      (u : LaurentPolynomial K) = Polynomial.toLaurent p * T (-(m : ℤ)) := by
        rw [hp, mul_T_assoc, add_neg_cancel, T_zero, mul_one]
      _ = C c * T ((i : ℤ) - m) := by
        rw [hpmon, Polynomial.toLaurent_C_mul_X_pow, mul_T_assoc, sub_eq_add_neg]
  · rintro ⟨c, n, hc, rfl⟩
    exact (hc.map C).mul (isUnit_T n)

/-- The coordinate on the punctured normalized line is never a d-th
power of a unit when d is at least two. -/
theorem laurent_T_one_not_unit_pow {d : ℕ} (hd : 2 ≤ d)
    (u : (LaurentPolynomial K)ˣ) : (u : LaurentPolynomial K) ^ d ≠ T 1 := by
  intro h
  obtain ⟨c, n, _, hu⟩ := (laurent_isUnit_iff_monomial K _).mp u.isUnit
  rw [hu, mul_pow, ← map_pow, T_pow, ← single_eq_C_mul_T] at h
  change AddMonoidAlgebra.single ((d : ℤ) * n) (c ^ d) =
    AddMonoidAlgebra.single 1 (1 : K) at h
  have he : (d : ℤ) * n = 1 := by
    by_contra hn
    have hc := congrArg (fun f : LaurentPolynomial K => f.coeff (1 : ℤ)) h
    exact zero_ne_one (by
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hn, if_pos rfl] using hc)
  have hnat : d * n.natAbs = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs he
  have hdiv : d ∣ 1 := ⟨n.natAbs, hnat.symm⟩
  have hd1 : d = 1 := Nat.dvd_one.mp hdiv
  omega

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``laurent_isUnit_iff_monomial, ``laurent_T_one_not_unit_pow] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.LaurentUnits
