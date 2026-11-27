import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexAnalytic

/-!
# The literal outside series at complex reciprocal arguments

Physical p. 314 gives the inverted summand with the squared finite product.
On every smaller disk a positive real infinite product bounds all finite
complex denominators away from zero.
-/

namespace ManuscriptAudit.Paper8ExteriorComplex

open Filter Paper8InsideComplexAnalytic
open scoped Topology

noncomputable section

def exteriorTerm (n : ℕ) (q : ℂ) : ℂ := q ^ n / pochhammer q n ^ 2

def exterior (q : ℂ) : ℂ := ∑' n : ℕ, exteriorTerm n q

def radialFloor (r : ℝ) : ℝ := ∏' j : ℕ, (1 - r ^ (j + 1))

theorem radius_power_le {r : ℝ} (hr : 0 ≤ r) (h₁ : r ≤ 1) (j : ℕ) :
    r ^ (j + 1) ≤ r := by
  have hPow : r ^ j ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hr h₁ j
  calc
    r ^ (j + 1) = r * r ^ j := pow_succ' r j
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hPow hr
    _ = r := mul_one r

private theorem radialFactor_pos {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) (j : ℕ) :
    0 < 1 - r ^ (j + 1) :=
  sub_pos.mpr ((radius_power_le hr h₁.le j).trans_lt h₁)

private theorem neg_radius_powers_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun j : ℕ => -(r ^ (j + 1))) := by
  simpa only [pow_succ', ← neg_mul] using
    (summable_geometric_of_lt_one hr h₁).mul_left (-r)

theorem radialFloor_pos {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) : 0 < radialFloor r := by
  have hLog : Summable (fun j : ℕ => Real.log (1 - r ^ (j + 1))) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable (neg_radius_powers_summable hr h₁)
  rw [radialFloor, ← Real.rexp_tsum_eq_tprod (radialFactor_pos hr h₁) hLog]
  exact Real.exp_pos _

private theorem radialFloor_le_partial {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) (n : ℕ) :
    radialFloor r ≤ ∏ j ∈ Finset.range n, (1 - r ^ (j + 1)) := by
  have hProd : Multipliable (fun j : ℕ => 1 - r ^ (j + 1)) := by
    simpa only [sub_eq_add_neg] using
      Real.multipliable_one_add_of_summable (neg_radius_powers_summable hr h₁)
  refine le_of_tendsto hProd.tendsto_prod_tprod_nat ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono hm)
    (fun j _ => (radialFactor_pos hr h₁ j).le)
    (fun j _ _ => sub_le_self _ (pow_nonneg hr (j + 1)))

private theorem radialFactor_le_norm {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (j : ℕ) :
    1 - r ^ (j + 1) ≤ ‖1 + q ^ (j + 1)‖ := by
  have hPow : ‖q ^ (j + 1)‖ ≤ r ^ (j + 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hqr _
  have h := norm_sub_norm_le (1 : ℂ) (-(q ^ (j + 1)))
  rw [norm_one, norm_neg, sub_neg_eq_add] at h
  exact (sub_le_sub_left hPow 1).trans h

private theorem pochhammer_succ (q : ℂ) (n : ℕ) :
    pochhammer q (n + 1) = pochhammer q n * (1 + q ^ (n + 1)) := by
  simp only [pochhammer, Finset.prod_range_succ]

theorem pochhammer_uniform_lower {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    radialFloor r ≤ ‖pochhammer q n‖ := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  refine (radialFloor_le_partial hr h₁ n).trans ?_
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
      rw [Finset.prod_range_succ, pochhammer_succ, norm_mul]
      exact mul_le_mul ih (radialFactor_le_norm hqr n)
        (radialFactor_pos hr h₁ n).le (norm_nonneg _)

theorem exteriorTerm_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖exteriorTerm n q‖ ≤ r ^ n / (radialFloor r) ^ 2 := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  have hFloor := radialFloor_pos hr h₁
  rw [exteriorTerm, norm_div, norm_pow, norm_pow]
  calc
    _ ≤ r ^ n / ‖pochhammer q n‖ ^ 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg q) hqr _) (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hr _) (sq_pos_of_pos hFloor)
      (pow_le_pow_left₀ hFloor.le (pochhammer_uniform_lower hqr h₁ n) 2)

theorem radialMajorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ n / (radialFloor r) ^ 2) := by
  simpa only [div_eq_mul_inv] using (summable_geometric_of_lt_one hr h₁).mul_right
    ((radialFloor r) ^ 2)⁻¹

theorem exterior_absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖exteriorTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => exteriorTerm_bound le_rfl hq n)
    (radialMajorant_summable (norm_nonneg q) hq)

theorem inverse_pochhammer_square (q : ℂ) (hq : q ≠ 0) (n : ℕ) :
    (pochhammer q⁻¹ n) ^ 2 * q ^ (n * (n + 1)) = (pochhammer q n) ^ 2 := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
      have hExp : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
      have hFactor : (1 + (q⁻¹) ^ (n + 1)) * q ^ (n + 1) = 1 + q ^ (n + 1) := by
        rw [add_mul, one_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
        exact add_comm _ _
      change (pochhammer q⁻¹ (n + 1)) ^ 2 * q ^ ((n + 1) * (n + 1 + 1)) =
        (pochhammer q (n + 1)) ^ 2
      rw [pochhammer_succ q⁻¹ n, pochhammer_succ q n, hExp,
        pow_add q (n * (n + 1)) ((n + 1) * 2), pow_mul q (n + 1) 2]
      calc
        _ = ((pochhammer q⁻¹ n) ^ 2 * q ^ (n * (n + 1))) *
            (((1 + (q⁻¹) ^ (n + 1)) * q ^ (n + 1)) ^ 2) := by ring
        _ = _ := by rw [ih, hFactor, mul_pow]

theorem exterior_term_eq {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    standardTerm n q⁻¹ = exteriorTerm n q := by
  have hExp : n * (n + 1) = n ^ 2 + n := by ring
  have hNum : (q⁻¹) ^ (n ^ 2) * q ^ (n * (n + 1)) = q ^ n := by
    rw [inv_pow, hExp, pow_add q (n ^ 2) n, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hq₀), one_mul]
  have hDenom : pochhammer q⁻¹ n ≠ 0 := by
    intro h
    have h' := inverse_pochhammer_square q hq₀ n
    simp only [h, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] at h'
    exact (pow_ne_zero 2 (pochhammer_ne_zero hq n)) h'.symm
  unfold standardTerm exteriorTerm
  apply (div_eq_div_iff (pow_ne_zero 2 hDenom) (pow_ne_zero 2 (pochhammer_ne_zero hq n))).2
  rw [← inverse_pochhammer_square q hq₀ n]
  calc
    _ = ((q⁻¹) ^ (n ^ 2) * q ^ (n * (n + 1))) * (pochhammer q⁻¹ n) ^ 2 := by ring
    _ = _ := by rw [hNum]

theorem standard_inv_eq_exterior {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    standard q⁻¹ = exterior q := by
  unfold standard exterior
  simp_rw [exterior_term_eq hq₀ hq]

theorem absolute_summability_at_inverse {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n => ‖standardTerm n q⁻¹‖) := by
  simp_rw [exterior_term_eq hq₀ hq]
  exact exterior_absolute_summability hq

end
end ManuscriptAudit.Paper8ExteriorComplex

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorComplex.radialFloor_pos,
      ``ManuscriptAudit.Paper8ExteriorComplex.pochhammer_uniform_lower,
      ``ManuscriptAudit.Paper8ExteriorComplex.exteriorTerm_bound,
      ``ManuscriptAudit.Paper8ExteriorComplex.exterior_absolute_summability,
      ``ManuscriptAudit.Paper8ExteriorComplex.inverse_pochhammer_square,
      ``ManuscriptAudit.Paper8ExteriorComplex.exterior_term_eq,
      ``ManuscriptAudit.Paper8ExteriorComplex.standard_inv_eq_exterior,
      ``ManuscriptAudit.Paper8ExteriorComplex.absolute_summability_at_inverse] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
