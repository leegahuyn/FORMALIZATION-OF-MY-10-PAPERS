import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Lucas

/-!
# The Hasse coefficient in the printed cubic family

The characteristic-p fiber of the Paper 5 profile is \(y^2=x^3+A\).
The coefficient of \(x^{q-1}\) in \((x^3+A)^{(q-1)/2}\) vanishes
for \(q=p^r\), \(r>0\), when \(p\equiv2\pmod 3\). This file computes the
polynomial coefficient. Its comparison with geometric Frobenius is a
separate result.
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


private theorem mod_eq_of_linear_congruence {p a n d : ℕ} [Fact p.Prime]
    (ha : 0 < a) (hap : a < p) (hdp : d < p)
    (hn : p ∣ a * n + 1) (hd : p ∣ a * d + 1) : n % p = d := by
  have hzn : (a : ZMod p) * (n : ZMod p) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff (a * n + 1) p).mpr hn
  have hzd : (a : ZMod p) * (d : ZMod p) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff (a * d + 1) p).mpr hd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hap, ZMod.val_zero] at hv
    exact ha.ne' hv
  have he : (n : ZMod p) = (d : ZMod p) :=
    mul_left_cancel₀ ha0 (add_right_cancel (hzn.trans hzd.symm))
  calc
    n % p = (n : ZMod p).val := (ZMod.val_natCast p n).symm
    _ = (d : ZMod p).val := congrArg ZMod.val he
    _ = d := ZMod.val_natCast_of_lt hdp

/-- When the cubic index is integral, the corresponding binomial
coefficient is divisible by the residue prime. -/
theorem cubic_binomial_choose_dvd {p r : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp3 : p % 3 = 2) (hr : 0 < r)
    (hc : 3 ∣ p ^ r - 1) :
    p ∣ Nat.choose ((p ^ r - 1) / 2) ((p ^ r - 1) / 3) := by
  let q := p ^ r
  let N := (q - 1) / 2
  let M := (q - 1) / 3
  have hp : p.Prime := Fact.out
  have hqpos : 0 < q := pow_pos hp.pos r
  have hqp : p ∣ q := dvd_pow_self p hr.ne'
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp (hodd.pow (n := r))
  have hq3 : (q - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc
  have hN : 2 * N + 1 = q := by dsimp [N]; omega
  have hM : 3 * M + 1 = q := by dsimp [M]; omega
  have h2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  have h3 : 3 * ((2 * p - 1) / 3) + 1 = 2 * p := by omega
  have hNdigit : N % p = (p - 1) / 2 :=
    mod_eq_of_linear_congruence (p := p) (a := 2) (n := N) (d := (p - 1) / 2)
      (by decide) (by omega) (by omega)
      (by simpa only [hN] using hqp) (by simpa only [h2] using (dvd_rfl : p ∣ p))
  have hMdigit : M % p = (2 * p - 1) / 3 :=
    mod_eq_of_linear_congruence (p := p) (a := 3) (n := M) (d := (2 * p - 1) / 3)
      (by decide) (by omega) (by omega)
      (by simpa only [hM] using hqp)
      (by simpa only [h3] using (dvd_mul_left p 2 : p ∣ 2 * p))
  have hlt : (p - 1) / 2 < (2 * p - 1) / 3 := by omega
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := N) (k := M)
  rw [hNdigit, hMdigit, Nat.choose_eq_zero_of_lt hlt, zero_mul] at hlucas
  exact Nat.modEq_zero_iff_dvd.mp hlucas

/-- The cubic coefficient vanishes for every extension degree \(r>0\)
in characteristic \(p\), for \(p\geq 5\) and \(p\equiv 2\pmod 3\). -/
theorem paper5_cubic_prime_power_coefficient_zero {R : Type*} [CommSemiring R]
    {p r : ℕ} [Fact p.Prime] [CharP R p] (a : R)
    (hp5 : 5 ≤ p) (hp3 : p % 3 = 2) (hr : 0 < r) :
    (((X : Polynomial R) ^ 3 + C a) ^ ((p ^ r - 1) / 2)).coeff (p ^ r - 1) = 0 := by
  by_cases hc : 3 ∣ p ^ r - 1
  · have h :
        ((X : Polynomial R) ^ 3 + C a) ^ ((p ^ r - 1) / 2) =
          expand R 3 (((X : Polynomial R) + C a) ^ ((p ^ r - 1) / 2)) := by
      simp only [map_pow, map_add, expand_X, expand_C]
    have hcast :
        (Nat.choose ((p ^ r - 1) / 2) ((p ^ r - 1) / 3) : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).mpr (cubic_binomial_choose_dvd hp5 hp3 hr hc)
    rw [h, coeff_expand (by decide : 0 < (3 : ℕ)), if_pos hc,
      coeff_X_add_C_pow, hcast, mul_zero]
  · exact cubic_pow_coeff_eq_zero_of_not_dvd a ((p ^ r - 1) / 2) (p ^ r - 1) hc

end ManuscriptAudit.CubicHasse

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHasse.cubic_pow_coeff_eq_zero_of_not_dvd,
      ``ManuscriptAudit.CubicHasse.paper5_cubic_hasse_coefficient_zero,
      ``ManuscriptAudit.CubicHasse.cubic_binomial_choose_dvd,
      ``ManuscriptAudit.CubicHasse.paper5_cubic_prime_power_coefficient_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
