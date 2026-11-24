import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic

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
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hn, if_true] using hc)
  have hnat : d * n.natAbs = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast,
      show Int.natAbs (1 : ℤ) = 1 from rfl] using congrArg Int.natAbs he
  have hdiv : d ∣ 1 := ⟨n.natAbs, hnat.symm⟩
  have hd1 : d = 1 := Nat.dvd_one.mp hdiv
  omega


private theorem laurent_monomial_pow (c : K) (n : ℤ) (d : ℕ) :
    (C c * T n : LaurentPolynomial K) ^ d =
      C (c ^ d) * T ((d : ℤ) * n) := by
  rw [mul_pow, ← map_pow, T_pow]

private theorem exponent_eq_of_monomial_eq {a b : K} {m n : ℤ}
    (hb : b ≠ 0) (h : (C a * T m : LaurentPolynomial K) = C b * T n) : m = n := by
  by_contra hne
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T] at h
  have hc := congrArg (fun f : LaurentPolynomial K => f.coeff n) h
  have hz : (0 : K) = b := by
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg hne, if_true] using hc
  exact hb hz.symm

/-- Over an algebraically closed field, the Laurent unit \(cT^n\) is a
\(d\)-th power of a unit exactly when \(d\) divides \(n\). -/
theorem laurent_monomial_unit_pow_iff [IsAlgClosed K] {d : ℕ} (hd : 0 < d)
    {c : K} (hc : c ≠ 0) (n : ℤ) :
    (∃ v : (LaurentPolynomial K)ˣ,
      (v : LaurentPolynomial K) ^ d = C c * T n) ↔ (d : ℤ) ∣ n := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨a, m, _, hm⟩ := (laurent_isUnit_iff_monomial K _).mp v.isUnit
    rw [hm, laurent_monomial_pow] at hv
    exact ⟨m, (exponent_eq_of_monomial_eq K hc hv).symm⟩
  · rintro ⟨m, hm⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c hd
    have ha0 : a ≠ 0 := by
      intro haz
      subst a
      rw [zero_pow (Nat.ne_of_gt hd)] at ha
      exact hc ha.symm
    obtain ⟨v, hv⟩ := ((isUnit_iff_ne_zero.mpr ha0).map C).mul (isUnit_T m)
    refine ⟨v, ?_⟩
    rw [hv, laurent_monomial_pow, ha, hm]

/-- Every Laurent unit is a \(d\)-th power times \(T^r\) for a
remainder exponent \(0\le r<d\). -/
theorem laurent_unit_has_power_residue [IsAlgClosed K] {d : ℕ} (hd : 0 < d)
    (u : (LaurentPolynomial K)ˣ) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (d : ℤ) ∧ ∃ v : (LaurentPolynomial K)ˣ,
      (u : LaurentPolynomial K) = (v : LaurentPolynomial K) ^ d * T r := by
  obtain ⟨c, n, hc, hn⟩ := (laurent_isUnit_iff_monomial K _).mp u.isUnit
  have hd' : (0 : ℤ) < (d : ℤ) := by omega
  let q : ℤ := n / (d : ℤ)
  let r : ℤ := n % (d : ℤ)
  have hi : (d : ℤ) * q + r = n := by
    change (d : ℤ) * (n / (d : ℤ)) + n % (d : ℤ) = n
    rw [mul_comm, add_comm]
    exact Int.emod_add_ediv_mul n (d : ℤ)
  obtain ⟨v, hv⟩ :=
    (laurent_monomial_unit_pow_iff K hd hc.ne_zero ((d : ℤ) * q)).mpr ⟨q, rfl⟩
  refine ⟨r, Int.emod_nonneg n (ne_of_gt hd'), Int.emod_lt_of_pos n hd', v, ?_⟩
  rw [hv, mul_T_assoc, hi, hn]

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``laurent_isUnit_iff_monomial, ``laurent_T_one_not_unit_pow,
      ``laurent_monomial_unit_pow_iff, ``laurent_unit_has_power_residue] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.LaurentUnits
