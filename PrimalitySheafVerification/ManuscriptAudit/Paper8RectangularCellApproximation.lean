import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ParametricCellMean

/-! A rectangular cell average approximates a smooth function with a mesh-size energy bound. -/

namespace ManuscriptAudit.Paper8RectangularCellApproximation

open MeasureTheory Set Paper8IntervalCellApproximation Paper8ParametricCellMean

noncomputable section

def rectangularCellMean (F : ℝ → ℝ → ℂ) (a b c d : ℝ) : ℂ :=
  intervalCellMean (fun y => intervalCellMean (fun x => F x y) a b) c d

private theorem norm_sq_sub_split_le (p m q : ℂ) :
    ‖p - q‖ ^ 2 ≤ 2 * ‖p - m‖ ^ 2 + 2 * ‖m - q‖ ^ 2 := by
  have h : p - q = (p - m) + (m - q) := by ring
  have hN : ‖p - q‖ ≤ ‖p - m‖ + ‖m - q‖ := by rw [h]; exact norm_add_le _ _
  have hP := pow_le_pow_left₀ (norm_nonneg _) hN 2
  nlinarith [sq_nonneg (‖p - m‖ - ‖m - q‖)]

theorem rectangular_cell_mean_l2_error_le {F X Y : ℝ → ℝ → ℂ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2))
    (hY : Continuous (fun p : ℝ × ℝ => Y p.1 p.2))
    (hx : ∀ x y, HasDerivAt (fun t => F t y) (X x y) x)
    (hy : ∀ x y, HasDerivAt (fun t => F x t) (Y x y) y)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    (∫ y in c..d, ∫ x in a..b, ‖F x y - rectangularCellMean F a b c d‖ ^ 2) ≤
      (2 * (b - a) ^ 2) * (∫ y in c..d, ∫ x in a..b, ‖X x y‖ ^ 2) +
      (2 * (d - c) ^ 2) * (∫ y in c..d, ∫ x in a..b, ‖Y x y‖ ^ 2) := by
  let L := b - a
  let M := d - c
  let G (y : ℝ) := intervalCellMean (fun x => F x y) a b
  let G' (y : ℝ) := intervalCellMean (fun x => Y x y) a b
  let m := intervalCellMean G c d
  let eX (y : ℝ) := ∫ x in a..b, ‖X x y‖ ^ 2
  let eY (y : ℝ) := ∫ x in a..b, ‖Y x y‖ ^ 2
  let q (y : ℝ) := ‖G y - m‖ ^ 2
  let K (y : ℝ) := ∫ x in a..b, ‖F x y - m‖ ^ 2
  have hL : 0 < L := sub_pos.mpr hab
  have hGc : Continuous G := continuous_intervalCellMean_param hF hab.le
  have hG'c : Continuous G' := continuous_intervalCellMean_param hY hab.le
  have hGd (y : ℝ) : HasDerivAt G (G' y) y := hasDerivAt_intervalCellMean_param hF hY hy hab.le y
  have heX : Continuous eX := continuous_intervalIntegral_param (hX.norm.pow 2) hab.le
  have heY : Continuous eY := continuous_intervalIntegral_param (hY.norm.pow 2) hab.le
  have hq : Continuous q := (hGc.sub continuous_const).norm.pow 2
  have hK : Continuous K := continuous_intervalIntegral_param ((hF.sub continuous_const).norm.pow 2) hab.le
  have hInX (y : ℝ) : K y ≤ 2 * L ^ 2 * eX y + (2 * L) * q y := by
    have hF₁ : Continuous (fun x => F x y) := hF.comp (continuous_id.prodMk continuous_const)
    have hX₁ : Continuous (fun x => X x y) := hX.comp (continuous_id.prodMk continuous_const)
    have hLocal : (∫ x in a..b, ‖F x y - G y‖ ^ 2) ≤ L ^ 2 * eX y :=
      interval_cell_mean_l2_error_le (fun x => hx x y) hX₁ hab
    have hA : IntervalIntegrable (fun x => 2 * ‖F x y - G y‖ ^ 2) volume a b :=
      (((hF₁.sub continuous_const).norm.pow 2).intervalIntegrable _ _).const_mul _
    have hB : IntervalIntegrable (fun _ : ℝ => 2 * q y) volume a b :=
      continuous_const.intervalIntegrable _ _
    calc
      K y ≤ ∫ x in a..b, 2 * ‖F x y - G y‖ ^ 2 + 2 * q y :=
        intervalIntegral.integral_mono_on hab.le
          (((hF₁.sub continuous_const).norm.pow 2).intervalIntegrable _ _) (hA.add hB)
          (fun x _ => norm_sq_sub_split_le (F x y) (G y) m)
      _ = 2 * (∫ x in a..b, ‖F x y - G y‖ ^ 2) + (2 * L) * q y := by
        rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul]
        change _ + L * (2 * q y) = _
        ring
      _ ≤ _ := by
        rw [mul_assoc 2 (L ^ 2)]
        exact add_le_add (mul_le_mul_of_nonneg_left hLocal (by norm_num)) le_rfl
  have hYLocal (y : ℝ) : ‖G' y‖ ^ 2 ≤ eY y / L :=
    norm_sq_intervalCellMean_le (hY.comp (continuous_id.prodMk continuous_const)) hab
  have hYInt : (∫ y in c..d, ‖G' y‖ ^ 2) ≤ (∫ y in c..d, eY y) / L := by
    calc
      _ ≤ ∫ y in c..d, eY y / L :=
        intervalIntegral.integral_mono_on hcd.le ((hG'c.norm.pow 2).intervalIntegrable _ _)
          ((heY.div_const L).intervalIntegrable _ _) (fun y _ => hYLocal y)
      _ = _ := by simp_rw [div_eq_mul_inv, intervalIntegral.integral_mul_const]
  have hQInt : (∫ y in c..d, q y) ≤ M ^ 2 * ((∫ y in c..d, eY y) / L) :=
    (interval_cell_mean_l2_error_le hGd hG'c hcd).trans
      (mul_le_mul_of_nonneg_left hYInt (sq_nonneg _))
  change (∫ y in c..d, K y) ≤
    (2 * L ^ 2) * (∫ y in c..d, eX y) + (2 * M ^ 2) * (∫ y in c..d, eY y)
  have hXInt : IntervalIntegrable (fun y => (2 * L ^ 2) * eX y) volume c d :=
    (heX.intervalIntegrable _ _).const_mul _
  have hQI : IntervalIntegrable (fun y => (2 * L) * q y) volume c d :=
    (hq.intervalIntegrable _ _).const_mul _
  calc
    _ ≤ ∫ y in c..d, (2 * L ^ 2) * eX y + (2 * L) * q y :=
      intervalIntegral.integral_mono_on hcd.le (hK.intervalIntegrable _ _) (hXInt.add hQI)
        (fun y _ => hInX y)
    _ = (2 * L ^ 2) * (∫ y in c..d, eX y) + (2 * L) * (∫ y in c..d, q y) := by
      rw [intervalIntegral.integral_add hXInt hQI, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (2 * L ^ 2) * (∫ y in c..d, eX y) + (2 * L) * (M ^ 2 * ((∫ y in c..d, eY y) / L)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hQInt (by positivity))
    _ = _ := by field_simp [hL.ne'] <;> ring

end
end ManuscriptAudit.Paper8RectangularCellApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8RectangularCellApproximation.rectangular_cell_mean_l2_error_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
