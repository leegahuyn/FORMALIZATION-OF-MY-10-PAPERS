import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryProduct

/-! Normalized and infinite-product-tail sums for the ordinary exterior series. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinarySums

open Paper8EulerianRecurrenceTerms
open Paper8ExteriorOrdinaryProduct
open Paper8ExteriorNormalization (negPochhammer ramanujanF exterior_eq_tsum)

noncomputable section

def W (q a : ℝ) : ℝ := U q a * U q a⁻¹

def DTerm (q a : ℝ) (n : ℕ) : ℝ := q ^ n / (product q a n * product q a⁻¹ n)

def D (q a : ℝ) : ℝ := ∑' n : ℕ, DTerm q a n

def JTerm (q a : ℝ) (n : ℕ) : ℝ := q ^ n * U q (a * q ^ n) * U q (a⁻¹ * q ^ n)

def J (q a : ℝ) : ℝ := ∑' n : ℕ, JTerm q a n

theorem one_le_W {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) : 1 ≤ W q a :=
  one_le_mul_of_one_le_of_one_le (one_le_U hq h₁ ha) (one_le_U hq h₁ (inv_nonneg.mpr ha))

theorem DTerm_nonneg {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ DTerm q a n :=
  div_nonneg (pow_nonneg hq _) (mul_nonneg ((zero_le_one).trans (product_ge_one hq ha n))
    ((zero_le_one).trans (product_ge_one hq (inv_nonneg.mpr ha) n)))

theorem DTerm_le_geometric {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (n : ℕ) :
    DTerm q a n ≤ q ^ n :=
  div_le_self (pow_nonneg hq _) (one_le_mul_of_one_le_of_one_le (product_ge_one hq ha n)
    (product_ge_one hq (inv_nonneg.mpr ha) n))

theorem D_summable {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    Summable (DTerm q a) :=
  Summable.of_nonneg_of_le (DTerm_nonneg hq ha) (DTerm_le_geometric hq ha)
    (summable_geometric_of_lt_one hq h₁)

theorem D_abs_le_geometric {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    |D q a| ≤ (1 - q)⁻¹ := by
  have hBound (n : ℕ) : ‖DTerm q a n‖ ≤ q ^ n := by
    rw [Real.norm_of_nonneg (DTerm_nonneg hq ha n)]
    exact DTerm_le_geometric hq ha n
  simpa only [D, Real.norm_eq_abs] using
    tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq h₁) hBound

theorem JTerm_eq_W_mul_DTerm {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (n : ℕ) :
    JTerm q a n = W q a * DTerm q a n := by
  have hb : 0 ≤ a⁻¹ := inv_nonneg.mpr ha
  have hp : product q a n ≠ 0 := (zero_lt_one.trans_le (product_ge_one hq ha n)).ne'
  have hp' : product q a⁻¹ n ≠ 0 := (zero_lt_one.trans_le (product_ge_one hq hb n)).ne'
  rw [JTerm, U_tail_eq_div hq h₁ ha n, U_tail_eq_div hq h₁ hb n, W, DTerm]
  field_simp [hp, hp'] <;> ring

theorem J_summable {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    Summable (JTerm q a) :=
  ((D_summable hq h₁ ha).mul_left (W q a)).congr (fun n => (JTerm_eq_W_mul_DTerm hq h₁ ha n).symm)

theorem J_eq_W_mul_D {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    J q a = W q a * D q a := by
  unfold J D
  simp_rw [JTerm_eq_W_mul_DTerm hq h₁ ha]
  exact (D_summable hq h₁ ha).tsum_mul_left _

theorem inverse_parameter_mul {q a : ℝ} (hq : 0 < q) (ha : 0 < a) :
    (a * q)⁻¹ * q = a⁻¹ := by
  field_simp [hq.ne', ha.ne'] <;> ring

theorem W_shift {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) :
    (1 + a * q) * W q (a * q) = (1 + a⁻¹) * W q a := by
  have hInv := U_step hq.le h₁ ((a * q)⁻¹)
  rw [inverse_parameter_mul hq ha] at hInv
  calc
    _ = ((1 + a * q) * U q (a * q)) * U q ((a * q)⁻¹) := by rw [W, mul_assoc]
    _ = _ := by rw [← U_step hq.le h₁ a, hInv, W]; ring

theorem W_one_eq_correction_denominator (q : ℝ) :
    W q 1 = (Paper8ExteriorProductCorrection.correctionProduct q) ^ 2 := by
  simp only [W, inv_one, U_one_eq_product_correction_denominator, pow_two]

theorem D_one_eq_literal_exterior {q : ℝ} (hq : 0 < q) :
    D q 1 = ramanujanF q⁻¹ := by
  rw [D, exterior_eq_tsum hq]
  refine tsum_congr fun n => ?_
  simp only [DTerm, inv_one, product, one_mul, negPochhammer, pow_two]

end
end ManuscriptAudit.Paper8ExteriorOrdinarySums

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.one_le_W,
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.D_abs_le_geometric,
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.J_eq_W_mul_D,
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.W_shift,
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.W_one_eq_correction_denominator,
      ``ManuscriptAudit.Paper8ExteriorOrdinarySums.D_one_eq_literal_exterior] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
