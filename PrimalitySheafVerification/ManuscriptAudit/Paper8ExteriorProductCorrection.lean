import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorNormalization

/-!
# A counterexample for the unilateral partial theta and product correction

The definitions printed on pp. 323 and 331 use a unilateral partial theta
and an independent product correction. At q = (1/2)^24 their combination
is strictly larger than the literal normalized exterior mock theta series.
-/

namespace ManuscriptAudit.Paper8ExteriorProductCorrection

open Paper8ExteriorNormalization

noncomputable section

/-- The unilateral partial theta of pp. 323 and 331, indexed by n+1. -/
def unilateralTheta (q : ℝ) : ℝ :=
  ∑' n : ℕ, partialThetaTerm q ((n + 1 : ℕ) : ℤ)

/-- The alternating triangular-exponent numerator of the product correction. -/
def correctionNumeratorTerm (q : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * q ^ (n * (n + 1) / 2)

/-- The denominator before squaring, the literal infinite Pochhammer product. -/
def correctionProduct (q : ℝ) : ℝ := ∏' j : ℕ, (1 + q ^ (j + 1))

/-- The separate product formula for S on pp. 323 and 331. -/
def productCorrection (q : ℝ) : ℝ :=
  (∑' n : ℕ, correctionNumeratorTerm q n) / (correctionProduct q) ^ 2

theorem unilateralTheta_summable_abs {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    Summable (fun n : ℕ => |partialThetaTerm q ((n + 1 : ℕ) : ℤ)|) := by
  let inclusion : ℕ → ℤ := fun n => ((n + 1 : ℕ) : ℤ)
  change Summable ((fun m : ℤ => |partialThetaTerm q m|) ∘ inclusion)
  apply (partialTheta_summable_abs hq h1).comp_injective
  intro m n h
  exact Nat.add_right_cancel (Int.ofNat.inj h)

theorem correctionProduct_multipliable {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    Multipliable (fun j : ℕ => 1 + q ^ (j + 1)) := by
  apply Real.multipliable_one_add_of_summable
  simpa only [pow_succ'] using (summable_geometric_of_lt_one hq.le h1).mul_left q

private theorem correctionProduct_ge_one {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    1 ≤ correctionProduct q :=
  le_hasProd_of_le_prod (correctionProduct_multipliable hq h1).hasProd (fun s =>
    Finset.one_le_prod (fun n _ => le_add_of_nonneg_right (pow_nonneg hq.le (n + 1))))

private theorem triangular_exponent_ge (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => decide
  | succ n =>
    have h := Nat.mul_le_mul_left (n + 1) (show 2 ≤ n + 1 + 1 by omega)
    rw [Nat.mul_comm (n + 1) 2] at h
    change n + 1 ≤ (n + 1) * (n + 1 + 1) / 2
    omega

private theorem correctionNumerator_abs_le {q : ℝ} (hq : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    |correctionNumeratorTerm q n| ≤ q ^ n := by
  rw [correctionNumeratorTerm, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hq _)]
  exact pow_le_pow_of_le_one hq h1 (triangular_exponent_ge n)

theorem correctionNumerator_summable_abs {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    Summable (fun n : ℕ => |correctionNumeratorTerm q n|) :=
  (summable_geometric_of_lt_one hq.le h1).of_nonneg_of_le (fun _ => abs_nonneg _)
    (correctionNumerator_abs_le hq.le h1.le)

theorem productCorrection_abs_le {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    |productCorrection q| ≤ (1 - q)⁻¹ := by
  have hNumerator : |∑' n : ℕ, correctionNumeratorTerm q n| ≤ (1 - q)⁻¹ := by
    simpa only [Real.norm_eq_abs] using
      (tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq.le h1)
        (f := correctionNumeratorTerm q) (fun n => by
          rw [Real.norm_eq_abs]
          exact correctionNumerator_abs_le hq.le h1.le n))
  have hProduct := correctionProduct_ge_one hq h1
  have hSquare : 1 ≤ (correctionProduct q) ^ 2 := by
    rw [pow_two]
    exact one_le_mul_of_one_le_of_one_le hProduct hProduct
  rw [productCorrection, abs_div, abs_of_nonneg (sq_nonneg (correctionProduct q))]
  exact (div_le_self (abs_nonneg _) hSquare).trans hNumerator

theorem exterior_le_geometric {q : ℝ} (hq : 0 < q) (h1 : q < 1) :
    ramanujanF q⁻¹ ≤ (1 - q)⁻¹ := by
  calc
    ramanujanF q⁻¹ ≤ ∑' n : ℕ, q ^ n := by
      apply Summable.tsum_le_tsum _ (exterior_summable hq h1)
        (summable_geometric_of_lt_one hq.le h1)
      intro n
      rw [exterior_term_eq hq]
      have hp : 1 ≤ negPochhammer q n :=
        Finset.one_le_prod (fun j _ => le_add_of_nonneg_right (pow_nonneg hq.le (j + 1)))
      apply div_le_self (pow_nonneg hq.le _)
      rw [pow_two]
      exact one_le_mul_of_one_le_of_one_le hp hp
    _ = _ := tsum_geometric_of_lt_one hq.le h1

def testQ : ℝ := ((1 : ℝ) / 2) ^ (24 : ℕ)

private theorem testQ_pos : 0 < testQ := by norm_num [testQ]
private theorem testQ_lt_one : testQ < 1 := by norm_num [testQ]

private theorem testQ_rpow_quadratic (m : ℕ) (hm : 1 ≤ m) :
    testQ ^ ((((m : ℤ) : ℝ) ^ 2 - 1) / 24) = ((1 : ℝ) / 2) ^ (m ^ 2 - 1) := by
  have hSquare : 1 ≤ m ^ 2 := by
    simpa only [pow_two, one_mul] using Nat.mul_le_mul hm hm
  rw [testQ, ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 : ℝ) / 2) 24,
    ← Real.rpow_natCast ((1 : ℝ) / 2) (m ^ 2 - 1), Nat.cast_sub hSquare]
  congr 1 <;> push_cast <;> ring

private theorem abs_cast_kronecker_le_one (m : ℤ) :
    |(kroneckerNegTwelve m : ℝ)| ≤ 1 := by
  have hJ : |(jacobiSym (-12) m.natAbs : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy (-12) m.natAbs with h | h | h <;> simp [h]
  unfold kroneckerNegTwelve
  split_ifs
  · simp
  · simpa only [Int.cast_neg, abs_neg] using hJ
  · exact hJ

private theorem unilateralTail_norm_le (n : ℕ) :
    ‖partialThetaTerm testQ ((n + 2 : ℕ) : ℤ)‖ ≤ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ n := by
  have hExponent : 2 * n + 3 ≤ (n + 2) ^ 2 - 1 := by
    rw [show (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 by ring]
    omega
  rw [Real.norm_eq_abs, partialThetaTerm, testQ_rpow_quadratic (n + 2) (by omega),
    abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : 0 ≤ (1 : ℝ) / 2) _)]
  calc
    _ ≤ 1 * ((1 : ℝ) / 2) ^ ((n + 2) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right (abs_cast_kronecker_le_one ((n + 2 : ℕ) : ℤ))
        (pow_nonneg (by norm_num : 0 ≤ (1 : ℝ) / 2) _)
    _ ≤ ((1 : ℝ) / 2) ^ (2 * n + 3) := by
      rw [one_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hExponent
    _ = _ := by
      rw [pow_add, pow_mul]
      norm_num <;> ring

theorem unilateralTheta_testQ_ge : (5 : ℝ) / 6 ≤ unilateralTheta testQ := by
  have hGeo : HasSum (fun n : ℕ => (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ n) (1 / 6 : ℝ) := by
    have hValue : (1 / 8 : ℝ) * (1 - (1 / 4 : ℝ))⁻¹ = (1 / 6 : ℝ) := by norm_num
    simpa only [hValue] using
      (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (1 / 8 : ℝ)
  have hTail := hGeo.summable.of_norm_bounded unilateralTail_norm_le
  have hBound : |∑' n : ℕ, partialThetaTerm testQ ((n + 2 : ℕ) : ℤ)| ≤ (1 / 6 : ℝ) := by
    simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hGeo unilateralTail_norm_le
  have hFirst : partialThetaTerm testQ ((0 + 1 : ℕ) : ℤ) = 1 := by
    norm_num [partialThetaTerm, kroneckerNegTwelve, jacobiSym.one_right, Real.rpow_zero]
  rw [unilateralTheta, tsum_eq_zero_add'
    (f := fun n : ℕ => partialThetaTerm testQ ((n + 1 : ℕ) : ℤ)) hTail, hFirst]
  have hLower := (abs_le.mp hBound).1
  change (5 : ℝ) / 6 ≤ 1 + ∑' n : ℕ, partialThetaTerm testQ ((n + 2 : ℕ) : ℤ)
  linarith

theorem normalized_exterior_testQ_lt_unilateral_product :
    normalizedG testQ⁻¹ < 2 * unilateralTheta testQ - productCorrection testQ := by
  have hPow : (testQ⁻¹) ^ (-(1 : ℝ) / 24) = (1 : ℝ) / 2 := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    have hExponent : -(-(1 : ℝ) / 24) = (1 : ℝ) / 24 := by ring
    rw [hExponent, testQ, ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 : ℝ) / 2) 24]
    norm_num
  have hGeo : (1 - testQ)⁻¹ < (10 : ℝ) / 9 := by norm_num [testQ]
  have hExterior := (exterior_le_geometric testQ_pos testQ_lt_one).trans_lt hGeo
  have hS := ((le_abs_self (productCorrection testQ)).trans
    (productCorrection_abs_le testQ_pos testQ_lt_one)).trans_lt hGeo
  rw [normalizedG, hPow]
  linarith [unilateralTheta_testQ_ge]

/-- Explicit counterexample to the normalized dictionary using the separate printed S. -/
theorem paper8_unilateral_product_dictionary_refuted :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ normalizedG q⁻¹ ≠ 2 * unilateralTheta q - productCorrection q :=
  ⟨testQ, testQ_pos, testQ_lt_one, normalized_exterior_testQ_lt_unilateral_product.ne⟩

end

end ManuscriptAudit.Paper8ExteriorProductCorrection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper8ExteriorProductCorrection.unilateralTheta_summable_abs,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.correctionProduct_multipliable,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.correctionNumerator_summable_abs,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.productCorrection_abs_le,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.exterior_le_geometric,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.unilateralTheta_testQ_ge,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.normalized_exterior_testQ_lt_unilateral_product,
        ``ManuscriptAudit.Paper8ExteriorProductCorrection.paper8_unilateral_product_dictionary_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
