import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The literal bound in the Rademacher tail

Paper 8, physical p. 351, uses the displayed half-order Bessel
expression and asks for a summable positive majorant in (G.2).
The actual terms of that majorant dominate a positive multiple of
the harmonic series for each nonzero polar family member.
-/

namespace ManuscriptAudit.PrintedRademacherTail

open Filter
open scoped Topology

noncomputable section

def printedBessel (x : ℝ) : ℝ :=
  Real.sqrt (Real.pi / (2 * x)) * Real.sinh x

theorem printedBessel_lower (x : ℝ) (hx : 0 < x) :
    Real.sqrt (Real.pi / 2) * Real.sqrt x ≤ printedBessel x := by
  have hPi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  calc
    _ = (Real.sqrt (Real.pi / 2) / Real.sqrt x) * x := by
      rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
    _ = Real.sqrt (Real.pi / (2 * x)) * x := by
      rw [show Real.pi / (2 * x) = (Real.pi / 2) / x by ring, Real.sqrt_div hPi]
    _ ≤ printedBessel x :=
      mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hx.le) (Real.sqrt_nonneg _)

/-- The exact exponential normalization of the printed Bessel expression. -/
theorem printedBessel_normalized (x : ℝ) (hx : 0 < x) :
    printedBessel x * Real.sqrt x * Real.exp (-x) =
      (Real.sqrt (Real.pi / 2) / 2) * (1 - Real.exp (-(2 * x))) := by
  have hPi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hRoot : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hFactor : Real.sqrt (Real.pi / (2 * x)) * Real.sqrt x =
      Real.sqrt (Real.pi / 2) := by
    rw [show Real.pi / (2 * x) = (Real.pi / 2) / x by ring,
      Real.sqrt_div hPi, div_mul_cancel₀ _ hRoot]
  have hOne : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hNeg : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hSinh : Real.sinh x * Real.exp (-x) =
      (1 - Real.exp (-(2 * x))) / 2 := by
    rw [Real.sinh_eq, div_mul_eq_mul_div, sub_mul, hOne, hNeg]
  calc
    _ = (Real.sqrt (Real.pi / (2 * x)) * Real.sqrt x) *
        (Real.sinh x * Real.exp (-x)) := by unfold printedBessel; ring
    _ = _ := by rw [hFactor, hSinh]; ring

theorem printedBessel_normalized_limit :
    Tendsto (fun x : ℝ => printedBessel x * Real.sqrt x * Real.exp (-x))
      atTop (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hlim : Tendsto (fun x : ℝ =>
      (Real.sqrt (Real.pi / 2) / 2) * (1 - Real.exp (-(2 * x))))
      atTop (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
    simpa only [sub_zero, mul_one] using
      (tendsto_const_nhds (x := Real.sqrt (Real.pi / 2) / 2)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (printedBessel_normalized x hx).symm

private theorem printedBessel_normalized_eventually_gt_half_limit :
    ∀ᶠ x : ℝ in atTop,
      (Real.sqrt (Real.pi / 2) / 2) / 2 < printedBessel x * Real.sqrt x * Real.exp (-x) := by
  have hC : 0 < Real.sqrt (Real.pi / 2) / 2 := by positivity
  exact (tendsto_order.1 printedBessel_normalized_limit).1 _ (by linarith)

/-- The normalization required for the printed n⁻³⁄⁴ leading-order
claim grows without bound, since its argument is proportional to √n. -/
theorem paper8_printed_wrong_power_normalization_diverges :
    Tendsto (fun x : ℝ =>
      x * (printedBessel x * Real.sqrt x * Real.exp (-x))) atTop atTop := by
  let C := Real.sqrt (Real.pi / 2) / 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hLower : Tendsto (fun x : ℝ => (C / 2) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (div_pos hC (by norm_num))
  have hNear : ∀ᶠ x in atTop, C / 2 < printedBessel x * Real.sqrt x * Real.exp (-x) :=
    printedBessel_normalized_eventually_gt_half_limit
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [(tendsto_atTop.1 hLower) M, hNear, eventually_ge_atTop (0 : ℝ)]
    with x hM hnx hx
  calc
    M ≤ (C / 2) * x := hM
    _ = x * (C / 2) := mul_comm _ _
    _ ≤ x * (printedBessel x * Real.sqrt x * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hnx.le hx

theorem paper8_printed_wrong_power_normalization_has_no_finite_limit (C : ℝ) :
    ¬ Tendsto (fun x : ℝ =>
      x * (printedBessel x * Real.sqrt x * Real.exp (-x))) atTop (𝓝 C) := by
  intro h
  have hSmall := (tendsto_order.1 h).2 (C + 1) (by linarith)
  have hLarge := (tendsto_atTop.1 paper8_printed_wrong_power_normalization_diverges) (C + 1)
  obtain ⟨x, hxSmall, hxLarge⟩ := (hSmall.and hLarge).exists
  exact (not_le_of_gt hxSmall) hxLarge

/-- The literal I expression from Paper 8 cannot obey an x⁻¹⁄²
envelope at large x. -/
theorem printedBessel_sqrt_scale_tendsto_atTop :
    Tendsto (fun x : ℝ => printedBessel x * Real.sqrt x) atTop atTop := by
  let c := (Real.sqrt (Real.pi / 2) / 2) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hLower : Tendsto (fun x : ℝ => c * Real.exp x) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [(tendsto_atTop.1 hLower) M, printedBessel_normalized_eventually_gt_half_limit]
    with x hM hnx
  calc
    M ≤ c * Real.exp x := hM
    _ = Real.exp x * c := mul_comm _ _
    _ ≤ Real.exp x * (printedBessel x * Real.sqrt x * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hnx.le (Real.exp_pos x).le
    _ = (printedBessel x * Real.sqrt x) * (Real.exp x * Real.exp (-x)) := by ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

private theorem harmonic_minorant (B c w : ℝ) (hB : 0 < B) (hc : 0 < c) (hw : 1 ≤ w) :
    (Real.sqrt (Real.pi / 2) * Real.sqrt B) / c ≤
      (w / Real.sqrt c) * printedBessel (B / c) := by
  have hRoot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hRadius := div_pos hB hc
  have hLower := printedBessel_lower (B / c) hRadius
  calc
    _ = (1 / Real.sqrt c) * (Real.sqrt (Real.pi / 2) * Real.sqrt (B / c)) := by
      symm
      rw [Real.sqrt_div hB.le]
      calc
        _ = (Real.sqrt (Real.pi / 2) * Real.sqrt B) /
            (Real.sqrt c * Real.sqrt c) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by rw [Real.mul_self_sqrt hc.le]
    _ ≤ (w / Real.sqrt c) * printedBessel (B / c) :=
      mul_le_mul (div_le_div_of_nonneg_right hw hRoot.le) hLower
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (div_nonneg (zero_le_one.trans hw) hRoot.le)

theorem printed_positive_majorant_not_summable
    (B : ℝ) (hB : 0 < B) (K : ℕ) (w : ℕ → ℝ) (hw : ∀ c, 0 < c → 1 ≤ w c) :
    ¬ Summable (fun j : ℕ =>
      (w (j + (K + 1)) / Real.sqrt (↑(j + (K + 1)) : ℝ)) *
        printedBessel (B / (↑(j + (K + 1)) : ℝ))) := by
  intro h
  let C := Real.sqrt (Real.pi / 2) * Real.sqrt B
  have hC : 0 < C := by dsimp [C]; positivity
  have hj (j : ℕ) : 0 < j + (K + 1) := by positivity
  have hcast (j : ℕ) : (0 : ℝ) < (↑(j + (K + 1)) : ℝ) := by exact_mod_cast hj j
  have hN : Summable (fun j : ℕ => C / (↑(j + (K + 1)) : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun j => div_nonneg hC.le (hcast j).le) _ h
    intro j
    exact harmonic_minorant B _ _ hB (hcast j) (hw _ (hj j))
  have hH : Summable (fun j : ℕ => 1 / (↑(j + (K + 1)) : ℝ)) := by
    refine (hN.mul_left C⁻¹).congr fun j => ?_
    change C⁻¹ * (C / (↑(j + (K + 1)) : ℝ)) = 1 / (↑(j + (K + 1)) : ℝ)
    rw [← mul_div_assoc, inv_mul_cancel₀ hC.ne']
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun j : ℕ => 1 / (j : ℝ)) (K + 1)).mp hH)

/-- The actual weight `τ(c) · √gcd(ℓ,n,c)` printed in (G.2). -/
def divisorWeight (ell n c : ℕ) : ℝ :=
  (c.divisors.card : ℝ) * Real.sqrt (ell.gcd (n.gcd c) : ℝ)

theorem paper8_printed_rademacher_tail_majorant_not_summable
    (ell n K : ℕ) (hell : 0 < ell) (hn : 0 < n) :
    ¬ Summable (fun j : ℕ =>
      (divisorWeight ell n (j + (K + 1)) /
        Real.sqrt (↑(j + (K + 1)) : ℝ)) *
      printedBessel (4 * Real.pi * Real.sqrt ((ell : ℝ) * (n : ℝ)) /
        (↑(j + (K + 1)) : ℝ))) := by
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply printed_positive_majorant_not_summable _ (by positivity)
  intro c hc
  have hdiv : 1 ≤ c.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hc.ne'⟩
  have hgcd : 1 ≤ ell.gcd (n.gcd c) :=
    Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right _ hc)
  have hdiv' : (1 : ℝ) ≤ c.divisors.card := by exact_mod_cast hdiv
  have hgcd' : (1 : ℝ) ≤ ell.gcd (n.gcd c) := by exact_mod_cast hgcd
  have hs : 1 ≤ Real.sqrt (ell.gcd (n.gcd c) : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hgcd'
  exact (one_mul (1 : ℝ)).ge.trans
    (mul_le_mul hdiv' hs zero_le_one (zero_le_one.trans hdiv'))

/-- If the same truncation tail is added to the complete sum and to
each partial sum, all partial sums must equal the complete sum. -/
theorem paper8_printed_double_counted_tail_forces_constant_partials
    (a full : ℂ) (partialSum tail : ℕ → ℂ)
    (hPrinted : ∀ K, a = full + tail K)
    (hTruncated : ∀ K, a = partialSum K + tail K) :
    ∀ K, partialSum K = full := by
  intro K
  exact add_right_cancel ((hTruncated K).symm.trans (hPrinted K))

end

end ManuscriptAudit.PrintedRademacherTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PrintedRademacherTail.printedBessel_lower,
      ``ManuscriptAudit.PrintedRademacherTail.printedBessel_normalized,
      ``ManuscriptAudit.PrintedRademacherTail.printedBessel_normalized_limit,
      ``ManuscriptAudit.PrintedRademacherTail.paper8_printed_wrong_power_normalization_diverges,
      ``ManuscriptAudit.PrintedRademacherTail.paper8_printed_wrong_power_normalization_has_no_finite_limit,
      ``ManuscriptAudit.PrintedRademacherTail.printedBessel_sqrt_scale_tendsto_atTop,
      ``ManuscriptAudit.PrintedRademacherTail.printed_positive_majorant_not_summable,
      ``ManuscriptAudit.PrintedRademacherTail.paper8_printed_rademacher_tail_majorant_not_summable,
      ``ManuscriptAudit.PrintedRademacherTail.paper8_printed_double_counted_tail_forces_constant_partials] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
