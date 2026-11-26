import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A fixed Paper 5 model with infinitely many trace-zero fibers

Paper 5, physical PDF pp. 157, 161–162. Choose the first prime, `pₙ = 2`,
and the allowed integer `A = 0` before varying the reduction prime.
The arithmetic trace is computed from the cardinality of Mathlib's
projective point group. The nonsquare `-1` makes the two quadratic
character contributions at `x` and `-x` cancel.
-/

namespace ManuscriptAudit.Paper5FixedTraceZero

open scoped BigOperators

noncomputable section

def fixedCurve : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -2
  a₆ := 0

def reduction (p : ℕ) : WeierstrassCurve (ZMod p) :=
  fixedCurve.map (Int.castRingHom (ZMod p))

theorem fixedCurve_discriminant : fixedCurve.Δ = 512 := by
  norm_num [fixedCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem reduction_discriminant_ne_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (reduction p).Δ ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv : (2 : ℕ) = 0 := by
      simpa only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega : 2 < p)] using
        congrArg ZMod.val h
    omega
  have hΔ : (reduction p).Δ = (2 : ZMod p) ^ 9 := by
    rw [reduction, WeierstrassCurve.map_Δ, fixedCurve_discriminant]
    norm_num
  rw [hΔ]
  exact pow_ne_zero 9 htwo

private def cubic (p : ℕ) (x : ZMod p) : ZMod p := x ^ 3 - 2 * x

abbrev AffineSolutions (p : ℕ) :=
  {xy : ZMod p × ZMod p // xy.2 ^ 2 = cubic p xy.1}

private theorem reduction_nonsingular_iff {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (x y : ZMod p) :
    (reduction p).toProjective.toAffine.Nonsingular x y ↔ y ^ 2 = cubic p x := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (reduction_discriminant_ne_zero hp), WeierstrassCurve.Affine.equation_iff]
  simp [reduction, fixedCurve, cubic, sub_eq_add_neg]

private def affineSigma (p : ℕ) :
    AffineSolutions p ≃ (Σ x : ZMod p, {y : ZMod p // y ^ 2 = cubic p x}) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, xy.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv xy := by cases xy; rfl
  right_inv z := by cases z; rfl

private theorem character_cubic_neg {p : ℕ} [Fact p.Prime] (hr : p % 4 = 3) (x : ZMod p) :
    quadraticChar (ZMod p) (cubic p (-x)) = -quadraticChar (ZMod p) (cubic p x) := by
  have hns : ¬ IsSquare (-1 : ZMod p) := by
    simp [FiniteField.isSquare_neg_one_iff, ZMod.card, hr]
  have hχ : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hns
  have hc : cubic p (-x) = (-1) * cubic p x := by
    unfold cubic
    ring
  rw [hc, map_mul, hχ, neg_one_mul]

private theorem character_cubic_sum_zero {p : ℕ} [Fact p.Prime] (hr : p % 4 = 3) :
    (∑ x : ZMod p, quadraticChar (ZMod p) (cubic p x)) = 0 := by
  have h : (∑ x : ZMod p, quadraticChar (ZMod p) (cubic p (-x))) =
      ∑ x : ZMod p, quadraticChar (ZMod p) (cubic p x) :=
    (Equiv.neg (ZMod p)).sum_comp (fun x => quadraticChar (ZMod p) (cubic p x))
  simp_rw [character_cubic_neg hr, Finset.sum_neg_distrib] at h
  omega

theorem affine_count {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    Nat.card (AffineSolutions p) = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar_zmod_n]
    omega
  have hfiber (x : ZMod p) :
      (Fintype.card {y : ZMod p // y ^ 2 = cubic p x} : ℤ) =
        quadraticChar (ZMod p) (cubic p x) + 1 := by
    simpa only [Set.toFinset_card] using quadraticChar_card_sqrts hchar (cubic p x)
  have hcast : (Fintype.card (AffineSolutions p) : ℤ) = (p : ℤ) := by
    rw [Fintype.card_congr (affineSigma p), Fintype.card_sigma, Nat.cast_sum]
    simp only [hfiber, Finset.sum_add_distrib, character_cubic_sum_zero hr, zero_add]
    simp [ZMod.card]
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hcast

private def projectiveEquiv {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (reduction p).toProjective.Point ≃ Option (AffineSolutions p) := by
  let W := (reduction p).toProjective
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ≃ AffineSolutions p :=
    { toFun := fun xy => ⟨xy.1, (reduction_nonsingular_iff hp _ _).1 xy.2⟩
      invFun := fun xy => ⟨xy.1, (reduction_nonsingular_iff hp _ _).2 xy.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans e₃.optionCongr)

theorem projective_count {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    Nat.card (reduction p).toProjective.Point = p + 1 := by
  classical
  calc
    Nat.card (reduction p).toProjective.Point = Nat.card (Option (AffineSolutions p)) :=
      Nat.card_congr (projectiveEquiv hp)
    _ = Nat.card (AffineSolutions p) + 1 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_option]
    _ = p + 1 := by rw [affine_count hp hr]

def arithmeticTrace (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (Nat.card (reduction p).toProjective.Point : ℤ)

theorem arithmeticTrace_eq_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    arithmeticTrace p = 0 := by
  unfold arithmeticTrace
  rw [projective_count hp hr]
  simp

private theorem exists_prime_three_mod_four_dvd (n : ℕ) (hn : n % 4 = 3) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ q ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    let q := n.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega : n ≠ 1)
    have hqn : q ∣ n := Nat.minFac_dvd n
    by_cases hq₃ : q % 4 = 3
    · exact ⟨q, hq, hq₃, hqn⟩
    · obtain ⟨m, hnm⟩ := hqn
      have hprod : ((q % 4) * (m % 4)) % 4 = 3 :=
        (Nat.mul_mod q m 4).symm.trans (by rw [← hnm, hn])
      have hq₀ : q % 4 ≠ 0 := by
        intro hz
        simp [hz] at hprod
      have hq₂ : q % 4 ≠ 2 := by
        intro he
        rw [he] at hprod
        omega
      have hq₁ : q % 4 = 1 := by
        have hb : q % 4 < 4 := Nat.mod_lt _ (by decide)
        omega
      have hm₃ : m % 4 = 3 := by simpa [hq₁] using hprod
      have hmul : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq.two_le
      have hlt : m < n := by omega
      obtain ⟨r, hr, hr₃, hrm⟩ := ih m hlt hm₃
      refine ⟨r, hr, hr₃, ?_⟩
      rw [hnm]
      exact dvd_mul_of_dvd_right hrm q

theorem arbitrarily_large_primes_three_mod_four (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ p % 4 = 3 := by
  let n := 4 * B.factorial - 1
  have hf : 0 < B.factorial := Nat.factorial_pos B
  have hn : n % 4 = 3 := by
    dsimp [n]
    omega
  obtain ⟨p, hp, hp₃, hpd⟩ := exists_prime_three_mod_four_dvd n hn
  refine ⟨p, ?_, hp, hp₃⟩
  by_contra hb
  have hpf : p ∣ B.factorial := Nat.dvd_factorial hp.pos (by omega)
  have hpm : p ∣ 4 * B.factorial := dvd_mul_of_dvd_right hpf 4
  have haux : 4 * B.factorial - n = 1 := by
    dsimp [n]
    omega
  exact hp.ne_one (Nat.dvd_one.mp (haux ▸ Nat.dvd_sub hpm hpd))

theorem arbitrarily_large_good_trace_zero_primes (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ 5 ≤ p ∧ p % 4 = 3 ∧
      (reduction p).Δ ≠ 0 ∧ arithmeticTrace p = 0 := by
  obtain ⟨p, hb, hp, hr⟩ := arbitrarily_large_primes_three_mod_four (max N 5)
  have hp₅ : 5 ≤ p := (le_max_right N 5).trans hb.le
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, (le_max_left N 5).trans_lt hb, hp, hp₅, hr,
    reduction_discriminant_ne_zero hp₅, arithmeticTrace_eq_zero hp₅ hr⟩

/-- The trace-zero set on the good-prime open is infinite for this one
integral model. This uses the arithmetic trace criterion of the paper. -/
theorem good_trace_zero_primes_infinite :
    {p : ℕ | p.Prime ∧ 5 ≤ p ∧ (reduction p).Δ ≠ 0 ∧ arithmeticTrace p = 0}.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨p, hpB, hp, hp₅, _, hΔ, htrace⟩ := arbitrarily_large_good_trace_zero_primes B
  exact (not_le_of_gt hpB) (hB ⟨hp, hp₅, hΔ, htrace⟩)

end

end ManuscriptAudit.Paper5FixedTraceZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5FixedTraceZero.fixedCurve_discriminant,
      ``ManuscriptAudit.Paper5FixedTraceZero.reduction_discriminant_ne_zero,
      ``ManuscriptAudit.Paper5FixedTraceZero.projective_count,
      ``ManuscriptAudit.Paper5FixedTraceZero.arithmeticTrace_eq_zero,
      ``ManuscriptAudit.Paper5FixedTraceZero.arbitrarily_large_good_trace_zero_primes,
      ``ManuscriptAudit.Paper5FixedTraceZero.good_trace_zero_primes_infinite] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
