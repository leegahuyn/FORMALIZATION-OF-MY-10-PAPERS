import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCuspPoincare

/-! A horizontal Floquet estimate for a finite family with a period-one energy bound. -/

namespace ManuscriptAudit.Paper8FloquetFamilyPoincare

open MeasureTheory Set
open Paper8OddCuspPoincare

noncomputable section

theorem floquet_family_point_norm_sq_le {ι : Type*} [Fintype ι] {q : ℂ} (hq : q ≠ 1)
    {F D : ι → ℝ → ℂ} {E : ℝ → ℝ}
    (hD : ∀ i x, HasDerivAt (F i) (D i x) x) (hDc : ∀ i, Continuous (D i))
    (hFl : ∀ i x, F i (x + 4) = q * F i x)
    (hEc : Continuous E) (hEp : Function.Periodic E 1)
    (hE : ∀ x, (∑ i, ‖D i x‖ ^ 2) ≤ E x) (a x : ℝ) :
    (∑ i, ‖F i x‖ ^ 2) ≤ (16 * ∫ t in a..a + 1, E t) / ‖q - 1‖ ^ 2 := by
  classical
  let Q := ‖q - 1‖ ^ 2
  let G (t : ℝ) := ∑ i, ‖D i t‖ ^ 2
  have hG : Continuous G := continuous_finsetSum _ (fun i _ => (hDc i).norm.pow 2)
  have hSum : (∑ i : ι, ∫ t in x..x + 4, ‖D i t‖ ^ 2) = ∫ t in x..x + 4, G t :=
    (intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun i t => ‖D i t‖ ^ 2) (fun i _ => ((hDc i).norm.pow 2).intervalIntegrable _ _)).symm
  have hFour : (∫ t in x..x + 4, E t) = 4 * ∫ t in a..a + 1, E t := by
    have h := hEp.intervalIntegral_add_zsmul_eq (4 : ℤ) x (fun a b => hEc.intervalIntegrable a b)
    rw [hEp.intervalIntegral_add_eq x a] at h
    simpa only [zsmul_eq_mul, Int.cast_ofNat, mul_one] using h
  have hInt : (∫ t in x..x + 4, G t) ≤ 4 * ∫ t in a..a + 1, E t := by
    rw [← hFour]
    exact intervalIntegral.integral_mono_on (by linarith)
      (hG.intervalIntegrable _ _) (hEc.intervalIntegrable _ _) (fun t _ => hE t)
  calc
    _ ≤ ∑ i, (4 * ∫ t in x..x + 4, ‖D i t‖ ^ 2) / Q :=
      Finset.sum_le_sum (fun i _ => floquet_point_norm_sq_le hq (hD i) (hDc i) (hFl i) x)
    _ = (4 * ∫ t in x..x + 4, G t) / Q := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hSum]
    _ ≤ (16 * ∫ t in a..a + 1, E t) / Q := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith only [hInt]

theorem floquet_family_strip_norm_sq_le {ι : Type*} [Fintype ι] {q : ℂ} (hq : q ≠ 1)
    {F D : ι → ℝ → ℂ} {E : ℝ → ℝ}
    (hD : ∀ i x, HasDerivAt (F i) (D i x) x) (hDc : ∀ i, Continuous (D i))
    (hFl : ∀ i x, F i (x + 4) = q * F i x)
    (hEc : Continuous E) (hEp : Function.Periodic E 1)
    (hE : ∀ x, (∑ i, ‖D i x‖ ^ 2) ≤ E x) (a : ℝ) :
    (∫ x in a..a + 1, ∑ i, ‖F i x‖ ^ 2) ≤
      (16 * ∫ x in a..a + 1, E x) / ‖q - 1‖ ^ 2 := by
  classical
  let C := (16 * ∫ x in a..a + 1, E x) / ‖q - 1‖ ^ 2
  have hF i : Continuous (F i) :=
    (show Differentiable ℝ (F i) from fun x => (hD i x).differentiableAt).continuous
  have hFc : Continuous (fun x => ∑ i, ‖F i x‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => (hF i).norm.pow 2)
  have hP (x : ℝ) : (∑ i, ‖F i x‖ ^ 2) ≤ C :=
    floquet_family_point_norm_sq_le hq hD hDc hFl hEc hEp hE a x
  calc
    _ ≤ ∫ _ in a..a + 1, C :=
      intervalIntegral.integral_mono_on (by linarith) (hFc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun x _ => hP x)
    _ = C := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

end
end ManuscriptAudit.Paper8FloquetFamilyPoincare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8FloquetFamilyPoincare.floquet_family_strip_norm_sq_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
