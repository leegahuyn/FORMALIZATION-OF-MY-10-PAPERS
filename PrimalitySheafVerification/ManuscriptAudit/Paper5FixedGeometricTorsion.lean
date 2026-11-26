import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.EllipticFiniteDescent
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount
import PrimalitySheafVerification.ManuscriptAudit.Paper5FixedTraceZero

/-!
# Geometric p-torsion of the fixed Paper 5 model

For the fixed integral model `y² = x³ - 2x`, reduction at any prime
`p ≡ 3 mod 4` with `p ≥ 5` has trivial geometric `p`-torsion.
The finite-field point count is computed modulo `p` in every finite
extension. The relevant coefficient vanishes by the lowest Lucas digit.
-/

namespace ManuscriptAudit.Paper5FixedGeometricTorsion

open Polynomial
open FiniteFieldPointCount (shortCubic)

noncomputable section

private theorem residue_of_linear_dvd {p a n d : ℕ} (hcop : p.Coprime a) (hd : d < p)
    (hn : p ∣ a * n + 1) (hd' : p ∣ a * d + 1) : n % p = d := by
  have hnum := (Nat.modEq_zero_iff_dvd.mpr hn).trans (Nat.modEq_zero_iff_dvd.mpr hd').symm
  have he := Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one
    (Nat.ModEq.add_right_cancel' 1 hnum)
  change n % p = d % p at he
  rwa [Nat.mod_eq_of_lt hd] at he

theorem quartic_index_choose_dvd {p r : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hp4 : p % 4 = 3) (hr : 0 < r) (hdiv : 4 ∣ p ^ r - 1) :
    p ∣ Nat.choose ((p ^ r - 1) / 2) ((p ^ r - 1) / 4) := by
  let q := p ^ r
  let N := (q - 1) / 2
  let M := (q - 1) / 4
  have hp : p.Prime := Fact.out
  have hqpos : 0 < q := pow_pos hp.pos r
  have hqp : p ∣ q := dvd_pow_self p hr.ne'
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp (hpodd.pow (n := r))
  have hq4 : (q - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hN : 2 * N + 1 = q := by dsimp [N]; omega
  have hM : 4 * M + 1 = q := by dsimp [M]; omega
  have h2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  have h4 : 4 * ((3 * p - 1) / 4) + 1 = 3 * p := by omega
  have hc₂ : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (fun h => by have := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) h; omega)
  have hc₄ : p.Coprime 4 := hp.coprime_iff_not_dvd.mpr
    (fun h => by have := Nat.le_of_dvd (by decide : 0 < (4 : ℕ)) h; omega)
  have hNdigit : N % p = (p - 1) / 2 :=
    residue_of_linear_dvd hc₂ (by omega)
      (by simpa only [hN] using hqp) (by simpa only [h2] using (dvd_rfl : p ∣ p))
  have hMdigit : M % p = (3 * p - 1) / 4 :=
    residue_of_linear_dvd hc₄ (by omega)
      (by simpa only [hM] using hqp) (by simpa only [h4] using (dvd_mul_left p 3 : p ∣ 3 * p))
  have hlt : (p - 1) / 2 < (3 * p - 1) / 4 := by omega
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := N) (k := M)
  rw [hNdigit, hMdigit, Nat.choose_eq_zero_of_lt hlt, zero_mul] at hlucas
  exact Nat.modEq_zero_iff_dvd.mp hlucas

theorem linear_cubic_prime_power_coefficient_zero {R : Type*} [CommRing R]
    {p r : ℕ} [Fact p.Prime] [CharP R p] (c : R)
    (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) (hr : 0 < r) :
    (((X : Polynomial R) ^ 3 - C c * X) ^ ((p ^ r - 1) / 2)).coeff (p ^ r - 1) = 0 := by
  let q := p ^ r
  let N := (q - 1) / 2
  have hp : p.Prime := Fact.out
  have hqpos : 0 < q := pow_pos hp.pos r
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow (n := r))
  have hN : q - 1 = N + N := by dsimp [N]; omega
  have hbase : (X : Polynomial R) ^ 3 - C c * X = X * (X ^ 2 + C (-c)) := by
    rw [map_neg]
    ring
  have hpow : (((X : Polynomial R) ^ 3 - C c * X) ^ N) =
      X ^ N * expand R 2 (((X : Polynomial R) + C (-c)) ^ N) := by
    rw [hbase, mul_pow]
    simp only [map_pow, map_add, expand_X, expand_C]
  change (((X : Polynomial R) ^ 3 - C c * X) ^ N).coeff (q - 1) = 0
  rw [hpow, hN, coeff_X_pow_mul, coeff_expand (by decide : 0 < (2 : ℕ))]
  split_ifs with h
  · have hdiv : 4 ∣ q - 1 := by
      obtain ⟨m, hm⟩ := h
      exact ⟨m, by omega⟩
    have hM : N / 2 = (q - 1) / 4 := by omega
    have hcast : (Nat.choose N (N / 2) : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).mpr
        (by rw [hM]; exact quartic_index_choose_dvd hp5 hp4 hr hdiv)
    rw [coeff_X_add_C_pow, hcast, mul_zero]
  · rfl

private theorem two_ne_zero {F : Type*} [Field F] {p : ℕ} [CharP F p] (hp5 : 5 ≤ p) :
    (2 : F) ≠ 0 := by
  have hn : ¬ p ∣ (2 : ℕ) := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) h
    omega
  simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero_iff F p 2).not.mpr hn

theorem shortCubic_linear_discriminant_ne_zero {F : Type*} [Field F]
    {p : ℕ} [CharP F p] (hp5 : 5 ≤ p) {c : F} (hc : c ≠ 0) :
    (shortCubic c (0 : F)).Δ ≠ 0 := by
  have hΔ : (shortCubic c (0 : F)).Δ = (2 : F) ^ 6 * c ^ 3 := by
    simp [shortCubic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> ring
  rw [hΔ]
  exact mul_ne_zero (pow_ne_zero 6 (two_ne_zero hp5)) (pow_ne_zero 3 hc)

theorem projective_count_cast_eq_one {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p) (hp4 : p % 4 = 3)
    {c : F} (hc : c ≠ 0) :
    (Nat.card (shortCubic c (0 : F)).toProjective.Point : F) = 1 := by
  classical
  let q := Fintype.card F
  let N := (q - 1) / 2
  let f := ((X : Polynomial F) ^ 3 - C c * X) ^ N
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; omega
  have hq : 1 < q := Fintype.one_lt_card
  have hbase : ((X : Polynomial F) ^ 3 - C c * X).natDegree ≤ 3 := by
    refine (natDegree_sub_le _ _).trans ?_
    have hlin : (C c * (X : Polynomial F)).natDegree ≤ 1 :=
      (natDegree_mul_le _ _).trans (by simp)
    exact max_le (by simp) (hlin.trans (by decide))
  have hdeg : f.natDegree < (q - 1) * 2 := by
    calc
      _ = N * ((X : Polynomial F) ^ 3 - C c * X).natDegree := natDegree_pow _ _
      _ ≤ N * 3 := Nat.mul_le_mul_left _ hbase
      _ < (q - 1) * 2 := by dsimp [N]; omega
  have he (x : F) : f.eval x = (x ^ 3 - c * x) ^ N := by simp [f]
  have hcoeff : f.coeff (q - 1) = 0 := by
    obtain ⟨r, _, hrank⟩ := FiniteField.card F p
    dsimp [f, N, q]
    rw [hrank]
    exact linear_cubic_prime_power_coefficient_zero c hp5 hp4 r.2
  rw [FiniteFieldPointCount.shortCubic_projective_count_cast hchar
    (shortCubic_linear_discriminant_ne_zero hp5 hc)]
  simp only [add_zero]
  change (1 : F) + (∑ x : F, (x ^ 3 - c * x) ^ N) = 1
  simp_rw [← he]
  rw [FiniteFieldPowerSums.finite_field_sum_eval_eq_neg_coeff F hq f hdeg, hcoeff,
    neg_zero, add_zero]

theorem torsion_eq_zero_of_card_cast_one {F G : Type*} [Field F] [AddGroup G]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hcard : (Nat.card G : F) = 1)
    (P : G) (hP : p • P = 0) : P = 0 := by
  let n := Nat.card G
  have hnd : ¬ p ∣ n := by
    intro h
    exact zero_ne_one (((CharP.cast_eq_zero_iff F p n).mpr h).symm.trans hcard)
  have hc : p.Coprime n := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnd
  have hd : addOrderOf P ∣ p.gcd n :=
    Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hP) (addOrderOf_dvd_natCard P)
  rw [hc.gcd_eq_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

private theorem reduction_baseChange_eq_short {p : ℕ} [Fact p.Prime] {L : Type*}
    [Field L] [Algebra (ZMod p) L] :
    (Paper5FixedTraceZero.reduction p).baseChange L = shortCubic (2 : L) 0 := by
  simp [Paper5FixedTraceZero.reduction, Paper5FixedTraceZero.fixedCurve, shortCubic,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

private theorem finite_affine_no_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Fintype L] [Algebra (ZMod p) L] (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) :
    ∀ Q : ((Paper5FixedTraceZero.reduction p).baseChange L).toAffine.Point,
      p • Q = 0 → Q = 0 := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  rw [reduction_baseChange_eq_short]
  intro Q hQ
  let e := (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := (shortCubic (2 : L) 0).toProjective)).symm
  have hT : p • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hcount := projective_count_cast_eq_one hp5 hp4 (two_ne_zero (F := L) hp5)
  have hz := torsion_eq_zero_of_card_cast_one hcount (e Q) hT
  apply e.injective
  simpa only [map_zero] using hz

theorem fixed_curve_no_geometric_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]
    (hp5 : 5 ≤ p) (hp4 : p % 4 = 3)
    (P : ((Paper5FixedTraceZero.reduction p).baseChange L).toProjective.Point)
    (hP : p • P = 0) : P = 0 := by
  classical
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := ((Paper5FixedTraceZero.reduction p).baseChange L).toProjective)
  apply e.injective
  rw [map_zero]
  refine EllipticFiniteDescent.torsion_eq_zero_of_finite_fields
    (Paper5FixedTraceZero.reduction p).toAffine p ?_ (e P) ?_
  · intro E hE
    letI : Finite E := hE
    letI := Fintype.ofFinite E
    exact finite_affine_no_p_torsion (L := E) hp5 hp4
  · rw [← map_nsmul, hP, map_zero]

def geometricTorsionTrivial (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ P : ((Paper5FixedTraceZero.reduction p).baseChange
      (AlgebraicClosure (ZMod p))).toProjective.Point, p • P = 0 → P = 0

theorem arbitrarily_large_good_geometric_torsion_trivial (N : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime), N < p ∧ p % 4 = 3 ∧
      (Paper5FixedTraceZero.reduction p).Δ ≠ 0 ∧ geometricTorsionTrivial p hp := by
  obtain ⟨p, hN, hp, hp5, hp4, hΔ, _⟩ :=
    Paper5FixedTraceZero.arbitrarily_large_good_trace_zero_primes N
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, hN, hp4, hΔ, fun P hP => fixed_curve_no_geometric_p_torsion hp5 hp4 P hP⟩

end

end ManuscriptAudit.Paper5FixedGeometricTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5FixedGeometricTorsion.quartic_index_choose_dvd,
      ``ManuscriptAudit.Paper5FixedGeometricTorsion.linear_cubic_prime_power_coefficient_zero,
      ``ManuscriptAudit.Paper5FixedGeometricTorsion.projective_count_cast_eq_one,
      ``ManuscriptAudit.Paper5FixedGeometricTorsion.fixed_curve_no_geometric_p_torsion,
      ``ManuscriptAudit.Paper5FixedGeometricTorsion.arbitrarily_large_good_geometric_torsion_trivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
