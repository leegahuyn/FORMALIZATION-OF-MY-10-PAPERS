import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The base Appell–Lerch numerator on physical PDF p. 305

This file treats the bilateral series in equation (*) with z = q^(1/2).
The base terms indexed by n and −n−1 cancel in an absolutely convergent
series. The theta denominator and the shifted families of D1 are outside
the scope of these declarations.
-/

namespace ManuscriptAudit.AppellLerchBase

noncomputable def appellTerm (z : ℂ) (n : ℤ) : ℂ :=
  z ^ (n * (n + 2)) / (1 - z ^ (2 * n + 1))

private theorem quotientInvFlip (c p : ℂ) (hp : p ≠ 0) :
    (c / p) / (1 - p⁻¹) = -(c / (1 - p)) := by
  have hprod : p * (1 - p⁻¹) = -(1 - p) := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hp]
    ring
  rw [← div_mul_eq_div_div, hprod, div_neg_eq_neg_div]

/-- The two reflected terms in the printed numerator are negatives. -/
theorem appellTerm_reflect {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    appellTerm z (-n - 1) = -appellTerm z n := by
  have hnum : (-n - 1) * (-n - 1 + 2) = n * (n + 2) - (2 * n + 1) := by ring
  have hden : 2 * (-n - 1) + 1 = -(2 * n + 1) := by ring
  unfold appellTerm
  rw [hnum, hden, zpow_sub₀ hz, zpow_neg]
  exact quotientInvFlip _ _ (zpow_ne_zero _ hz)

/-- All denominators of the bilateral series are nonzero in its annulus. -/
theorem appellDenominator_ne_zero {z : ℂ}
    (hpos : 0 < ‖z‖) (hlt : ‖z‖ < 1) (n : ℤ) :
    1 - z ^ (2 * n + 1) ≠ 0 := by
  intro h
  have heq : z ^ (2 * n + 1) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖z‖ ^ (2 * n + 1) = 1 := by
    rw [← norm_zpow, heq, norm_one]
  have hindex : (2 * n + 1 : ℤ) = 0 :=
    (zpow_right_strictAnti₀ hpos hlt).injective
      (by simpa only [zpow_zero] using hnorm)
  omega

private theorem norm_appellTerm_nat_le {z : ℂ}
    (hpos : 0 < ‖z‖) (hlt : ‖z‖ < 1) (n : ℕ) :
    ‖appellTerm z (n : ℤ)‖ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
  have hpow : ‖z‖ ^ (2 * (n : ℤ) + 1) ≤ ‖z‖ := by
    calc
      _ ≤ ‖z‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hpos hlt.le (by omega)
      _ = _ := zpow_one _
  have hden : 1 - ‖z‖ ≤ ‖1 - z ^ (2 * (n : ℤ) + 1)‖ := by
    calc
      _ ≤ 1 - ‖z‖ ^ (2 * (n : ℤ) + 1) := sub_le_sub_left hpow _
      _ = ‖(1 : ℂ)‖ - ‖z ^ (2 * (n : ℤ) + 1)‖ := by rw [norm_one, norm_zpow]
      _ ≤ _ := norm_sub_norm_le _ _
  have hindex : (n : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 2) := by
    calc
      (n : ℤ) = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hnum : ‖z‖ ^ ((n : ℤ) * ((n : ℤ) + 2)) ≤ ‖z‖ ^ n := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hpos hlt.le hindex
  rw [appellTerm, norm_div, norm_zpow]
  exact div_le_div₀ (pow_nonneg (norm_nonneg _) _) hnum (sub_pos.mpr hlt) hden

private theorem appellTerm_reflect_nat {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    appellTerm z (-((n : ℤ) + 1)) = -appellTerm z (n : ℤ) := by
  rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, appellTerm_reflect hz]

/-- The ordinary sum of norms of the actual bilateral terms is finite. -/
theorem summable_norm_appellTerm {z : ℂ} (hpos : 0 < ‖z‖) (hlt : ‖z‖ < 1) :
    Summable (fun n : ℤ => ‖appellTerm z n‖) := by
  have hz : z ≠ 0 := norm_pos_iff.mp hpos
  have hgeom : Summable (fun n : ℕ => ‖z‖ ^ n) :=
    summable_geometric_of_abs_lt_one (by simpa only [abs_of_nonneg hpos.le] using hlt)
  have hmajorant : Summable (fun n : ℕ => ‖z‖ ^ n / (1 - ‖z‖)) := by
    simpa only [div_eq_mul_inv] using hgeom.mul_right (1 - ‖z‖)⁻¹
  have hnat : Summable (fun n : ℕ => ‖appellTerm z (n : ℤ)‖) :=
    hmajorant.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_appellTerm_nat_le hpos hlt)
  have hneg : Summable (fun n : ℕ => ‖appellTerm z (-((n : ℤ) + 1))‖) := by
    simpa only [appellTerm_reflect_nat hz, norm_neg] using hnat
  exact hnat.of_nat_of_neg_add_one hneg

/-- Equation (*) has zero bilateral numerator throughout the punctured unit disk. -/
theorem hasSum_appellTerm_zero {z : ℂ} (hpos : 0 < ‖z‖) (hlt : ‖z‖ < 1) :
    HasSum (appellTerm z) 0 := by
  have hz : z ≠ 0 := norm_pos_iff.mp hpos
  have hs : Summable (appellTerm z) := (summable_norm_appellTerm hpos hlt).of_norm
  have hpaired := hs.hasSum.nat_add_neg_add_one
  have hfun : (fun n : ℕ => appellTerm z (n : ℤ) + appellTerm z (-((n : ℤ) + 1))) =
      (fun _ : ℕ => (0 : ℂ)) := by
    funext n
    rw [appellTerm_reflect_nat hz, add_neg_cancel]
  rw [hfun] at hpaired
  have htotal : (∑' n : ℤ, appellTerm z n) = 0 := hpaired.unique hasSum_zero
  rw [← htotal]
  exact hs.hasSum

/-- The paper's q^(1/2) is exp(π i τ), so the same conclusion holds on ℍ. -/
theorem hasSum_appellTerm_halfNome_zero (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (appellTerm (Complex.exp ((Real.pi : ℂ) * Complex.I * τ))) 0 := by
  refine hasSum_appellTerm_zero (norm_pos_iff.mpr (Complex.exp_ne_zero _)) ?_
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have hRe : (((Real.pi : ℂ) * Complex.I) * τ).re = -(Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hRe]
  exact neg_lt_zero.mpr (mul_pos Real.pi_pos hτ)

end ManuscriptAudit.AppellLerchBase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.AppellLerchBase.appellTerm_reflect,
    ``ManuscriptAudit.AppellLerchBase.appellDenominator_ne_zero,
    ``ManuscriptAudit.AppellLerchBase.summable_norm_appellTerm,
    ``ManuscriptAudit.AppellLerchBase.hasSum_appellTerm_zero,
    ``ManuscriptAudit.AppellLerchBase.hasSum_appellTerm_halfNome_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
