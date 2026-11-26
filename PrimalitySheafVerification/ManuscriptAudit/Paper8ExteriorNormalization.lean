import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The normalized exterior identity for Ramanujan's f

On physical p. 314, equation (3.4) defines S by subtracting the actual
outside f series from twice the bilateral partial theta series.
Equation (3.5) identifies the resulting right-hand side with G at the
reciprocal argument. For every positive q below one, the normalization
of G printed on pp. 324 and 332 gives a strictly smaller value.
-/

namespace ManuscriptAudit.Paper8ExteriorNormalization

open scoped BigOperators

noncomputable section

/-- The finite product `(-q;q)_n` in the mock theta series. -/
def negPochhammer (q : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 + q ^ (j + 1))

private theorem negPochhammer_succ (q : ℝ) (n : ℕ) :
    negPochhammer q (n + 1) = negPochhammer q n * (1 + q ^ (n + 1)) := by
  unfold negPochhammer
  rw [Finset.prod_range_succ]

private theorem one_le_negPochhammer {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    1 ≤ negPochhammer q n := by
  induction n with
  | zero => simp [negPochhammer]
  | succ n ih =>
    rw [negPochhammer_succ]
    exact one_le_mul_of_one_le_of_one_le ih (le_add_of_nonneg_right (pow_nonneg hq _))

private theorem negPochhammer_ne_zero {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    negPochhammer q n ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (one_le_negPochhammer hq n)).ne'

private theorem inverse_pochhammer_square (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    (negPochhammer q⁻¹ n) ^ 2 * q ^ (n * (n + 1)) = (negPochhammer q n) ^ 2 := by
  induction n with
  | zero => simp [negPochhammer]
  | succ n ih =>
    have hExp : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
    have hFactor : (1 + (q⁻¹) ^ (n + 1)) * q ^ (n + 1) = 1 + q ^ (n + 1) := by
      rw [add_mul, one_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
      exact add_comm _ _
    change (negPochhammer q⁻¹ (n + 1)) ^ 2 * q ^ ((n + 1) * (n + 1 + 1)) =
      (negPochhammer q (n + 1)) ^ 2
    rw [negPochhammer_succ q⁻¹ n, negPochhammer_succ q n, hExp,
      pow_add q (n * (n + 1)) ((n + 1) * 2), pow_mul q (n + 1) 2]
    calc
      _ = ((negPochhammer q⁻¹ n) ^ 2 * q ^ (n * (n + 1))) *
          (((1 + (q⁻¹) ^ (n + 1)) * q ^ (n + 1)) ^ 2) := by ring
      _ = _ := by rw [ih, hFactor, mul_pow]

/-- The unnormalized summand in Ramanujan's series for f. -/
def ramanujanTerm (q : ℝ) (n : ℕ) : ℝ :=
  q ^ (n ^ 2) / (negPochhammer q n) ^ 2

/-- The literal q-series for f, allowing the reciprocal argument. -/
def ramanujanF (q : ℝ) : ℝ := ∑' n : ℕ, ramanujanTerm q n

/-- At the reciprocal argument, the summand is the printed exterior summand. -/
theorem exterior_term_eq {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ramanujanTerm q⁻¹ n = q ^ n / (negPochhammer q n) ^ 2 := by
  have hExp : n * (n + 1) = n ^ 2 + n := by ring
  have hNum : (q⁻¹) ^ (n ^ 2) * q ^ (n * (n + 1)) = q ^ n := by
    rw [inv_pow, hExp, pow_add q (n ^ 2) n, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hq.ne'), one_mul]
  unfold ramanujanTerm
  apply (div_eq_div_iff
    (pow_ne_zero 2 (negPochhammer_ne_zero (inv_nonneg.2 hq.le) n))
    (pow_ne_zero 2 (negPochhammer_ne_zero hq.le n))).2
  rw [← inverse_pochhammer_square q hq.ne' n]
  calc
    _ = ((q⁻¹) ^ (n ^ 2) * q ^ (n * (n + 1))) * (negPochhammer q⁻¹ n) ^ 2 := by ring
    _ = _ := by rw [hNum]

private theorem exterior_term_nonneg {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 ≤ ramanujanTerm q⁻¹ n := by
  rw [exterior_term_eq hq]
  exact div_nonneg (pow_nonneg hq.le _) (sq_nonneg _)

/-- The literal exterior series converges on the positive unit interval. -/
theorem exterior_summable {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    Summable (ramanujanTerm q⁻¹) := by
  refine (summable_geometric_of_lt_one hq.le h1).of_nonneg_of_le (exterior_term_nonneg hq) ?_
  intro n
  rw [exterior_term_eq hq]
  have h := one_le_negPochhammer hq.le n
  apply div_le_self (pow_nonneg hq.le _)
  rw [pow_two]
  exact one_le_mul_of_one_le_of_one_le h h

/-- The exterior value is exactly the printed sum of the transformed terms. -/
theorem exterior_eq_tsum {q : ℝ} (hq : 0 < q) :
    ramanujanF q⁻¹ = ∑' n : ℕ, q ^ n / (negPochhammer q n) ^ 2 := by
  unfold ramanujanF
  simp_rw [exterior_term_eq hq]

/-- The constant term of the convergent exterior series gives a lower bound of one. -/
theorem one_le_exterior {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    1 ≤ ramanujanF q⁻¹ := by
  calc
    1 = ramanujanTerm q⁻¹ 0 := by simp [ramanujanTerm, negPochhammer]
    _ ≤ ramanujanF q⁻¹ := (exterior_summable hq h1).le_tsum 0 (fun n _ => exterior_term_nonneg hq n)

/-- The Kronecker symbol for numerator −12, using the Jacobi symbol
for positive odd denominators and the sign rule for negative denominators. -/
def kroneckerNegTwelve (m : ℤ) : ℤ :=
  if m % 2 = 0 then 0 else
    if m < 0 then -(jacobiSym (-12) m.natAbs) else jacobiSym (-12) m.natAbs

private theorem abs_cast_kronecker_le_one (m : ℤ) :
    |(kroneckerNegTwelve m : ℝ)| ≤ 1 := by
  have hJ : |(jacobiSym (-12) m.natAbs : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy (-12) m.natAbs with h | h | h <;> simp [h]
  unfold kroneckerNegTwelve
  split_ifs
  · simp
  · simpa only [Int.cast_neg, abs_neg] using hJ
  · exact hJ

/-- The literal bilateral partial theta summand from p. 314. -/
def partialThetaTerm (q : ℝ) (m : ℤ) : ℝ :=
  (kroneckerNegTwelve m : ℝ) * q ^ (((m : ℝ) ^ 2 - 1) / 24)

/-- The partial theta function occurring in the printed right-hand side. -/
def partialTheta (q : ℝ) : ℝ := ∑' m : ℤ, partialThetaTerm q m

/-- The bilateral partial theta sum is absolutely convergent in the comparison. -/
theorem partialTheta_summable_abs {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    Summable (fun m : ℤ => |partialThetaTerm q m|) := by
  let a := Real.log q / 24
  have ha : a < 0 := div_neg_of_neg_of_pos (Real.log_neg hq h1) (by norm_num)
  have hNat : Summable (fun n : ℕ => Real.exp (a * (n : ℝ) ^ 2)) := by
    apply Real.summable_exp_nat_mul_of_ge ha
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith [sq_nonneg (n : ℝ)]
  have hg : Summable (fun m : ℤ => Real.exp (a * (m : ℝ) ^ 2)) := by
    apply Summable.of_nat_of_neg
    · simpa only [Int.cast_natCast] using hNat
    · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hNat
  refine (hg.mul_left (Real.exp (-a))).of_nonneg_of_le (fun _ => abs_nonneg _) ?_
  intro m
  unfold partialThetaTerm
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  calc
    _ ≤ 1 * q ^ (((m : ℝ) ^ 2 - 1) / 24) :=
      mul_le_mul_of_nonneg_right (abs_cast_kronecker_le_one m) (Real.rpow_nonneg hq.le _)
    _ = _ := by
      rw [one_mul, ← Real.exp_add, Real.rpow_def_of_pos hq]
      congr 1
      dsimp [a]
      ring

/-- The correction S as defined by equation (3.4). -/
def correctionS (q : ℝ) : ℝ :=
  2 * partialTheta q - ramanujanF q⁻¹

/-- The normalization G as defined on pp. 324 and 332. -/
def normalizedG (q : ℝ) : ℝ :=
  q ^ (-(1 : ℝ) / 24) * ramanujanF q

/-- The two sides of the printed dictionary satisfy a strict inequality
for every positive q below one. -/
theorem normalized_exterior_lt_printed_rhs {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    normalizedG q⁻¹ < 2 * partialTheta q - correctionS q := by
  have hPow : (q⁻¹) ^ (-(1 : ℝ) / 24) = q ^ ((1 : ℝ) / 24) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hRight : 2 * partialTheta q - correctionS q = ramanujanF q⁻¹ := by
    unfold correctionS
    ring
  rw [normalizedG, hPow, hRight]
  have hpos : 0 < ramanujanF q⁻¹ := lt_of_lt_of_le zero_lt_one (one_le_exterior hq h1)
  have hpowlt : q ^ ((1 : ℝ) / 24) < 1 := Real.rpow_lt_one hq.le h1 (by norm_num)
  simpa only [one_mul] using mul_lt_mul_of_pos_right hpowlt hpos

/-- The p. 314 equations with the pp. 324 and 332 normalization fail on `0 < q < 1`. -/
theorem paper8_normalized_outside_dictionary_refuted {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    normalizedG q⁻¹ ≠ 2 * partialTheta q - correctionS q :=
  (normalized_exterior_lt_printed_rhs hq h1).ne

end

end ManuscriptAudit.Paper8ExteriorNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorNormalization.exterior_term_eq,
      ``ManuscriptAudit.Paper8ExteriorNormalization.exterior_summable,
      ``ManuscriptAudit.Paper8ExteriorNormalization.exterior_eq_tsum,
      ``ManuscriptAudit.Paper8ExteriorNormalization.one_le_exterior,
      ``ManuscriptAudit.Paper8ExteriorNormalization.partialTheta_summable_abs,
      ``ManuscriptAudit.Paper8ExteriorNormalization.normalized_exterior_lt_printed_rhs,
      ``ManuscriptAudit.Paper8ExteriorNormalization.paper8_normalized_outside_dictionary_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
