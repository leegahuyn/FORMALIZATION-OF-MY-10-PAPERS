import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Prime.Factorial
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricConverse
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicTrace

/-!
# Both trace profiles of the printed varying cubic family

When the prime is one modulo three, the Hasse coefficient is nonzero.
Lucas's formula also computes this coefficient over every prime-power
extension. At extension degree p−1 the actual point count is divisible
by p.
-/

namespace ManuscriptAudit.CubicTraceClassification

open Polynomial
open FiniteFieldPointCount
open PrimalitySheafVerification.ManuscriptAudit
  (paper5TraceCurve paper5_traceCurve_trace_eq_zero paper5_traceCurve_discriminant_ne_zero)

private def geometricSum (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + p * geometricSum p n

private theorem pow_sub_one_eq (p : ℕ) (hp : 0 < p) (r : ℕ) :
    p ^ r - 1 = (p - 1) * geometricSum p r := by
  induction r with
  | zero => simp [geometricSum]
  | succ r ih =>
    have hb : p ≤ p * p ^ r := by
      simpa only [mul_one] using Nat.mul_le_mul_left p (show 1 ≤ p ^ r from pow_pos hp r)
    calc
      p ^ (r + 1) - 1 = p * (p ^ r - 1) + (p - 1) := by
        rw [pow_succ', Nat.mul_sub, mul_one]
        omega
      _ = (p - 1) * geometricSum p (r + 1) := by
        rw [ih, geometricSum]
        ring

private theorem geometricSum_digit (p k r : ℕ) :
    k * geometricSum p (r + 1) = k + p * (k * geometricSum p r) := by
  rw [geometricSum]
  ring

private theorem choose_geometricSum_cast {p n k : ℕ} [Fact p.Prime]
    (hn : n < p) (hk : k < p) (r : ℕ) :
    (Nat.choose (n * geometricSum p r) (k * geometricSum p r) : ZMod p) =
      (Nat.choose n k : ZMod p) ^ r := by
  have hp : 0 < p := (show Nat.Prime p from Fact.out).pos
  induction r with
  | zero => simp [geometricSum]
  | succ r ih =>
    let N := n * geometricSum p (r + 1)
    let K := k * geometricSum p (r + 1)
    have hmN : N % p = n := by
      rw [N, geometricSum_digit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
    have hmK : K % p = k := by
      rw [K, geometricSum_digit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    have hdN : N / p = n * geometricSum p r := by
      rw [N, geometricSum_digit, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hn, zero_add]
    have hdK : K / p = k * geometricSum p r := by
      rw [K, geometricSum_digit, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hk, zero_add]
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := N) (k := K)
    have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
    change (Nat.choose N K : ZMod p) = _
    rw [hmN, hmK, hdN, hdK, Nat.cast_mul, ih] at hc
    rw [hc, pow_succ, mul_comm]

private theorem pow_prime_field {p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ p = x := by
  have hp : 0 < p := (show Nat.Prime p from Fact.out).pos
  by_cases hx : x = 0
  · rw [hx, zero_pow hp.ne']
  calc
    x ^ p = x ^ ((p - 1) + 1) := by congr 1; omega
    _ = x := by rw [pow_succ, ZMod.pow_card_sub_one_eq_one hx, one_mul]

private theorem scalar_geometricSum_pow {p : ℕ} [Fact p.Prime] (A : ZMod p) (k r : ℕ) :
    A ^ (k * geometricSum p r) = (A ^ k) ^ r := by
  induction r with
  | zero => simp [geometricSum]
  | succ r ih =>
    rw [geometricSum_digit, pow_add, pow_mul, pow_prime_field, ih, pow_succ, mul_comm]

private theorem choose_cast_ne_zero {p n m : ℕ} [Fact p.Prime]
    (hn : n < p) (hm : m ≤ n) : (Nat.choose n m : ZMod p) ≠ 0 := by
  intro h
  have hp : Nat.Prime p := Fact.out
  have hd := (ZMod.natCast_eq_zero_iff (Nat.choose n m) p).mp h
  have hd' : p ∣ Nat.choose n m * Nat.factorial m * Nat.factorial (n - m) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  rw [Nat.choose_mul_factorial_mul_factorial hm] at hd'
  exact (Nat.not_le_of_lt hn) (hp.dvd_factorial.mp hd')

/-- For the residue class one modulo three, the actual Hasse coefficient
on the degree-r extension is the rth power of the base coefficient. -/
theorem cubic_coefficient_primePower_eq_pow {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp3 : p % 3 = 1) (A : ZMod p) (r : ℕ) :
    (((X : Polynomial (ZMod p)) ^ 3 + C A) ^ ((p ^ r - 1) / 2)).coeff (p ^ r - 1) =
      (A ^ ((p - 1) / 2 - (p - 1) / 3) *
        (Nat.choose ((p - 1) / 2) ((p - 1) / 3) : ZMod p)) ^ r := by
  have hp : Nat.Prime p := Fact.out
  have hOdd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  let n := (p - 1) / 2
  let m := (p - 1) / 3
  have hn : n < p := by dsimp [n]; omega
  have hm : m < p := by dsimp [m]; omega
  have h2 : 2 * n = p - 1 := by dsimp [n]; omega
  have h3 : 3 * m = p - 1 := by dsimp [m]; omega
  have hPow := pow_sub_one_eq p hp.pos r
  have hd2 : (p ^ r - 1) / 2 = n * geometricSum p r := by
    rw [hPow, ← h2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < (2 : ℕ))]
  have hd3 : (p ^ r - 1) / 3 = m * geometricSum p r := by
    rw [hPow, ← h3, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < (3 : ℕ))]
  have hdvd : 3 ∣ p ^ r - 1 := by
    exact ⟨m * geometricSum p r, by rw [hPow, ← h3, Nat.mul_assoc]⟩
  have he :
      ((X : Polynomial (ZMod p)) ^ 3 + C A) ^ ((p ^ r - 1) / 2) =
        expand (ZMod p) 3 (((X : Polynomial (ZMod p)) + C A) ^ ((p ^ r - 1) / 2)) := by
    simp only [map_pow, map_add, expand_X, expand_C]
  rw [he, coeff_expand (by decide : 0 < (3 : ℕ)), if_pos hdvd, coeff_X_add_C_pow,
    hd2, hd3, ← Nat.sub_mul, scalar_geometricSum_pow, choose_geometricSum_cast hn hm, ← mul_pow]

private theorem cubic_coefficient_base_nonzero {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp3 : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) :
    (((X : Polynomial (ZMod p)) ^ 3 + C A) ^ ((p - 1) / 2)).coeff (p - 1) ≠ 0 := by
  have h := cubic_coefficient_primePower_eq_pow hp5 hp3 A 1
  rw [pow_one, pow_one] at h
  rw [h]
  exact mul_ne_zero (pow_ne_zero _ hA) (choose_cast_ne_zero (by omega) (by omega))

private theorem prime_rem_three_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    p % 3 ≠ 0 := by
  intro h
  have hp : Nat.Prime p := Fact.out
  have hd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h
  rcases (Nat.dvd_prime hp).mp hd with h' | h' <;> omega

/-- The literal smooth reductions in the varying family have trace zero
exactly at primes congruent to two modulo three. -/
theorem paper5_trace_eq_zero_iff {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) = 0 ↔ p % 3 = 2 := by
  classical
  refine ⟨?_, fun hr => paper5_traceCurve_trace_eq_zero hp5 hr hA⟩
  intro hz
  by_contra hne
  have hp3 := prime_rem_three_ne_zero (p := p) hp5
  have hres : p % 3 = 1 := by omega
  have hW : paper5TraceCurve p A = shortCubic (0 : ZMod p) A := by
    simp [paper5TraceCurve, shortCubic]
  have hΔ : (shortCubic (0 : ZMod p) A).Δ ≠ 0 := by
    simpa only [hW] using paper5_traceCurve_discriminant_ne_zero hp5 hA
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hcount := shortCubic_zero_count_cast_eq_one_sub_coeff hchar Fintype.one_lt_card hΔ
  have hCard : Nat.card (paper5TraceCurve p A).toProjective.Point = p + 1 := by omega
  rw [← hW, hCard, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add, ZMod.card] at hcount
  exact (cubic_coefficient_base_nonzero hp5 hres hA) (sub_eq_self.mp hcount.symm)

/-- The actual projective point count over a field of order p^(p−1)
is divisible by p in the complementary residue class. -/
theorem paper5_extension_count_dvd {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
    (hCard : Fintype.card F = p ^ (p - 1)) (hp5 : 5 ≤ p) (hp3 : p % 3 = 1)
    {A : ZMod p} (hA : A ≠ 0) :
    p ∣ Nat.card ((paper5TraceCurve p A).baseChange F).toProjective.Point := by
  letI : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  let a := algebraMap (ZMod p) F A
  have ha : a ≠ 0 := by
    simpa only [a, map_zero] using (algebraMap (ZMod p) F).injective.ne hA
  have hW : (paper5TraceCurve p A).baseChange F = shortCubic (0 : F) a := by
    simp [paper5TraceCurve, shortCubic, a, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; omega
  have hΔ := CubicFiniteTorsion.shortCubic_zero_discriminant_ne_zero p hp5 ha
  have hCount := shortCubic_zero_count_cast_eq_one_sub_coeff hchar Fintype.one_lt_card hΔ
  let q := p ^ (p - 1)
  let b := A ^ ((p - 1) / 2 - (p - 1) / 3) *
    (Nat.choose ((p - 1) / 2) ((p - 1) / 3) : ZMod p)
  have hb : b ≠ 0 := mul_ne_zero (pow_ne_zero _ hA) (choose_cast_ne_zero (by omega) (by omega))
  have hc : (((X : Polynomial (ZMod p)) ^ 3 + C A) ^ ((q - 1) / 2)).coeff (q - 1) = 1 := by
    calc
      _ = b ^ (p - 1) := cubic_coefficient_primePower_eq_pow hp5 hp3 A (p - 1)
      _ = 1 := ZMod.pow_card_sub_one_eq_one hb
  have hm : (((X : Polynomial (ZMod p)) ^ 3 + C A) ^ ((q - 1) / 2)).map
      (algebraMap (ZMod p) F) = ((X : Polynomial F) ^ 3 + C a) ^ ((q - 1) / 2) := by
    simp [a]
  have hCoeffF : (((X : Polynomial F) ^ 3 + C a) ^ ((q - 1) / 2)).coeff (q - 1) = 1 := by
    rw [← hm, Polynomial.coeff_map, hc, map_one]
  rw [hCard, hCoeffF, sub_self] at hCount
  rw [hW]
  exact (CharP.cast_eq_zero_iff F p _).mp hCount

/-- Actual geometric p-torsion of the printed varying family is trivial
exactly in the residue class two modulo three. -/
theorem paper5_trivial_geometric_p_torsion_iff {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    (∀ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
      p • P = 0 → P = 0) ↔ p % 3 = 2 := by
  classical
  refine ⟨?_, fun hr => CubicGeometricTorsion.paper5_no_p_torsion_over_algebraicClosure hp5 hr hA⟩
  intro h
  by_contra hn
  have h0 := prime_rem_three_ne_zero (p := p) hp5
  have hr : p % 3 = 1 := by omega
  let r := p - 1
  let F := GaloisField p r
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ (p - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p r (by dsimp [r]; omega)
  obtain ⟨P, hP, hz⟩ :=
    CubicGeometricConverse.paper5_geometric_p_torsion_of_galoisField_projective_card_dvd r
      (paper5_extension_count_dvd hc hp5 hr hA)
  exact hP (h P hz)

/-- Trace zero and trivial geometric p-torsion agree for every stated
good reduction of the printed varying family. -/
theorem paper5_trace_zero_iff_trivial_geometric_p_torsion {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    ((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) = 0) ↔
      (∀ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
        p • P = 0 → P = 0) :=
  (paper5_trace_eq_zero_iff hp5 hA).trans (paper5_trivial_geometric_p_torsion_iff hp5 hA).symm

end ManuscriptAudit.CubicTraceClassification

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicTraceClassification.cubic_coefficient_primePower_eq_pow,
      ``ManuscriptAudit.CubicTraceClassification.paper5_trace_eq_zero_iff,
      ``ManuscriptAudit.CubicTraceClassification.paper5_extension_count_dvd,
      ``ManuscriptAudit.CubicTraceClassification.paper5_trivial_geometric_p_torsion_iff,
      ``ManuscriptAudit.CubicTraceClassification.paper5_trace_zero_iff_trivial_geometric_p_torsion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
