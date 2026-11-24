import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

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


/-- Two reduced Laurent exponents representing the same class modulo
actual \(d\)-th powers of units coincide. -/
theorem laurent_T_reduced_residue_eq [IsAlgClosed K] {d : ℕ} (hd : 0 < d)
    {r s : ℤ} (hr0 : 0 ≤ r) (hrd : r < (d : ℤ)) (hs0 : 0 ≤ s) (hsd : s < (d : ℤ))
    (v : (LaurentPolynomial K)ˣ)
    (he : (T r : LaurentPolynomial K) = (v : LaurentPolynomial K) ^ d * T s) : r = s := by
  have hpow : (v : LaurentPolynomial K) ^ d = T (r - s) := by
    calc
      _ = (v : LaurentPolynomial K) ^ d * T s * T (-s) := by
        rw [mul_T_assoc, add_neg_cancel, T_zero, mul_one]
      _ = T r * T (-s) := congrArg (fun f : LaurentPolynomial K => f * T (-s)) he.symm
      _ = T (r - s) := by rw [sub_eq_add_neg, T_add]
  have hdvd : (d : ℤ) ∣ r - s :=
    (laurent_monomial_unit_pow_iff K hd (one_ne_zero : (1 : K) ≠ 0) (r - s)).mp
      ⟨v, by simpa only [map_one, one_mul] using hpow⟩
  have hm : Int.ModEq (d : ℤ) s r := Int.modEq_iff_dvd.mpr hdvd
  change s % (d : ℤ) = r % (d : ℤ) at hm
  rw [Int.emod_eq_of_lt hs0 hsd, Int.emod_eq_of_lt hr0 hrd] at hm
  exact hm.symm

/-- Each Laurent unit has exactly one reduced exponent representative. -/
theorem laurent_unit_has_unique_power_residue [IsAlgClosed K] {d : ℕ} (hd : 0 < d)
    (u : (LaurentPolynomial K)ˣ) :
    ∃! r : ℤ, 0 ≤ r ∧ r < (d : ℤ) ∧ ∃ v : (LaurentPolynomial K)ˣ,
      (u : LaurentPolynomial K) = (v : LaurentPolynomial K) ^ d * T r := by
  obtain ⟨r, hr0, hrd, v, hv⟩ := laurent_unit_has_power_residue K hd u
  refine ⟨r, ⟨hr0, hrd, v, hv⟩, ?_⟩
  rintro s ⟨hs0, hsd, w, hw⟩
  apply laurent_T_reduced_residue_eq K hd hs0 hsd hr0 hrd (w⁻¹ * v)
  have hcancel : (↑(w⁻¹) : LaurentPolynomial K) ^ d * (w : LaurentPolynomial K) ^ d = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  calc
    _ = (↑(w⁻¹) : LaurentPolynomial K) ^ d * ((w : LaurentPolynomial K) ^ d * T s) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = (↑(w⁻¹) : LaurentPolynomial K) ^ d * ((v : LaurentPolynomial K) ^ d * T r) :=
      congrArg (fun f : LaurentPolynomial K => (↑(w⁻¹) : LaurentPolynomial K) ^ d * f)
        (hw.symm.trans hv)
    _ = (↑(w⁻¹ * v) : LaurentPolynomial K) ^ d * T r := by
      rw [Units.val_mul, mul_pow, mul_assoc]

private theorem unit_exponent_exists (u : (LaurentPolynomial K)ˣ) :
    ∃ n : ℤ, ∃ c : K, IsUnit c ∧ (u : LaurentPolynomial K) = C c * T n := by
  obtain ⟨c, n, hc, hu⟩ := (laurent_isUnit_iff_monomial K _).mp u.isUnit
  exact ⟨n, c, hc, hu⟩

private noncomputable def unitExponent (u : (LaurentPolynomial K)ˣ) : ℤ :=
  Classical.choose (unit_exponent_exists K u)

private theorem unitExponent_spec (u : (LaurentPolynomial K)ˣ) :
    ∃ c : K, IsUnit c ∧ (u : LaurentPolynomial K) = C c * T (unitExponent K u) :=
  Classical.choose_spec (unit_exponent_exists K u)

private theorem unitExponent_of_monomial (u : (LaurentPolynomial K)ˣ) {c : K}
    (hc : IsUnit c) {n : ℤ} (hu : (u : LaurentPolynomial K) = C c * T n) :
    unitExponent K u = n := by
  obtain ⟨a, _, ha⟩ := unitExponent_spec K u
  exact exponent_eq_of_monomial_eq K hc.ne_zero (ha.symm.trans hu)

private noncomputable def unitExponentHom : (LaurentPolynomial K)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (unitExponent K u)
  map_one' := by
    change unitExponent K 1 = 0
    exact unitExponent_of_monomial K 1 (isUnit_one : IsUnit (1 : K)) (by simp)
  map_mul' u v := by
    change unitExponent K (u * v) = unitExponent K u + unitExponent K v
    obtain ⟨a, ha, hu⟩ := unitExponent_spec K u
    obtain ⟨b, hb, hv⟩ := unitExponent_spec K v
    apply unitExponent_of_monomial K (u * v) (ha.mul hb)
    rw [Units.val_mul, hu, hv, map_mul, T_add, mul_mul_mul_comm]

private noncomputable def unitResidue (d : ℕ) :
    (LaurentPolynomial K)ˣ →* Multiplicative (ZMod d) :=
  (Int.castAddHom (ZMod d)).toMultiplicative.comp (unitExponentHom K)

private theorem unitResidue_surjective (d : ℕ) :
    Function.Surjective (unitResidue K d) := by
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  obtain ⟨u, hu⟩ := (isUnit_T n : IsUnit (T n : LaurentPolynomial K))
  have hmon : (u : LaurentPolynomial K) = C (1 : K) * T n := by
    simpa only [map_one, one_mul] using hu
  refine ⟨u, ?_⟩
  change Multiplicative.ofAdd ((unitExponent K u : ℤ) : ZMod d) = x
  rw [unitExponent_of_monomial K u (isUnit_one : IsUnit (1 : K)) hmon, hn] <;> rfl

/-- The subgroup of actual \(d\)-th powers of Laurent polynomial units. -/
abbrev unitPowerSubgroup (d : ℕ) : Subgroup ((LaurentPolynomial K)ˣ) :=
  (powMonoidHom (α := (LaurentPolynomial K)ˣ) d).range

private theorem unitResidue_ker [IsAlgClosed K] {d : ℕ} (hd : 0 < d) :
    (unitResidue K d).ker = unitPowerSubgroup K d := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  change ((unitExponent K u : ℤ) : ZMod d) = 0 ↔
    ∃ v : (LaurentPolynomial K)ˣ, v ^ d = u
  rw [CharP.intCast_eq_zero_iff (ZMod d) d]
  obtain ⟨c, hc, hu⟩ := unitExponent_spec K u
  have hiff := laurent_monomial_unit_pow_iff K hd hc.ne_zero (unitExponent K u)
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hiff.mpr h
    refine ⟨v, Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val, hu] using hv
  · rintro ⟨v, hv⟩
    apply hiff.mp
    refine ⟨v, ?_⟩
    simpa only [Units.val_pow_eq_pow_val, hu] using congrArg Units.val hv

/-- The quotient by actual \(d\)-th unit powers is the cyclic group of
Laurent exponents modulo \(d\). -/
noncomputable def laurent_unit_power_quotient_equiv [IsAlgClosed K] {d : ℕ} (hd : 0 < d) :
    ((LaurentPolynomial K)ˣ ⧸ unitPowerSubgroup K d) ≃* Multiplicative (ZMod d) :=
  (QuotientGroup.quotientMulEquivOfEq (unitResidue_ker K hd).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (unitResidue K d) (unitResidue_surjective K d))

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``laurent_isUnit_iff_monomial, ``laurent_T_one_not_unit_pow,
      ``laurent_monomial_unit_pow_iff, ``laurent_unit_has_power_residue,
      ``laurent_T_reduced_residue_eq, ``laurent_unit_has_unique_power_residue,
      ``laurent_unit_power_quotient_equiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.LaurentUnits
