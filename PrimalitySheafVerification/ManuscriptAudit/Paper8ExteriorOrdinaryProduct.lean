import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrenceTerms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-! Infinite products and their exact tails for the corrected exterior identity. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryProduct

open Filter Paper8EulerianRecurrenceTerms
open scoped Topology

noncomputable section

def U (q a : ℝ) : ℝ := ∏' j : ℕ, (1 + a * q ^ (j + 1))

theorem U_multipliable {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (a : ℝ) :
    Multipliable (fun j : ℕ => 1 + a * q ^ (j + 1)) := by
  apply Real.multipliable_one_add_of_summable
  simpa only [pow_succ', mul_assoc] using (summable_geometric_of_lt_one hq h₁).mul_left (a * q)

theorem one_le_U {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) : 1 ≤ U q a :=
  le_hasProd_of_le_prod (U_multipliable hq h₁ a).hasProd fun s =>
    Finset.one_le_prod fun j _ => le_add_of_nonneg_right (mul_nonneg ha (pow_nonneg hq _))

theorem U_split {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (a : ℝ) (n : ℕ) :
    product q a n * U q (a * q ^ n) = U q a := by
  have hShift : (fun j : ℕ => 1 + a * q ^ ((j + n) + 1)) =
      (fun j : ℕ => 1 + (a * q ^ n) * q ^ (j + 1)) := by
    funext j
    rw [show j + n + 1 = n + (j + 1) by omega, pow_add q n (j + 1), mul_assoc]
  have hTail : Multipliable (fun j : ℕ => 1 + a * q ^ ((j + n) + 1)) := by
    rw [hShift]
    exact U_multipliable hq h₁ (a * q ^ n)
  have h := Multipliable.prod_mul_tprod_nat_mul' (f := fun j : ℕ => 1 + a * q ^ (j + 1)) (k := n) hTail
  change product q a n * tprod (fun j : ℕ => 1 + a * q ^ ((j + n) + 1)) = U q a at h
  rw [hShift] at h
  exact h

theorem U_step {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (a : ℝ) :
    U q a = (1 + a * q) * U q (a * q) := by
  simpa [product, Finset.prod_range_one] using (U_split hq h₁ a 1).symm

theorem U_tail_eq_div {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (n : ℕ) :
    U q (a * q ^ n) = U q a / product q a n := by
  have hNZ : product q a n ≠ 0 := (zero_lt_one.trans_le (product_ge_one hq ha n)).ne'
  apply (eq_div_iff hNZ).mpr
  rw [mul_comm, U_split hq h₁ a n]

theorem U_tail_tendsto_one {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => U q (a * q ^ n)) atTop (𝓝 1) := by
  have hProd : Tendsto (product q a) atTop (𝓝 (U q a)) :=
    (U_multipliable hq h₁ a).tendsto_prod_tprod_nat
  have hNZ : U q a ≠ 0 := (zero_lt_one.trans_le (one_le_U hq h₁ ha)).ne'
  have hRatio : Tendsto (fun n : ℕ => U q a / product q a n) atTop (𝓝 (U q a / U q a)) :=
    tendsto_const_nhds.div hProd hNZ
  simp_rw [U_tail_eq_div hq h₁ ha]
  simpa only [div_self hNZ] using hRatio

theorem U_one_eq_product_correction_denominator (q : ℝ) :
    U q 1 = Paper8ExteriorProductCorrection.correctionProduct q := by
  simp only [U, Paper8ExteriorProductCorrection.correctionProduct, one_mul]

end
end ManuscriptAudit.Paper8ExteriorOrdinaryProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryProduct.U_multipliable,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryProduct.one_le_U,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryProduct.U_split,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryProduct.U_tail_tendsto_one,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryProduct.U_one_eq_product_correction_denominator] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
