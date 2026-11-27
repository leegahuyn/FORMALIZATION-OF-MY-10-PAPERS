import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.CircleIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourGammaSeries
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase

/-!
# Individual contour integrals in physical p. 335

The literal PDF exponential coefficients are 2/3 in the numerator and
(2/3)·24 = 16 in the denominator. Rhoades uses 23 and 24, respectively,
in Theorem 1.1 and Section 3 of
https://arxiv.org/pdf/1111.1495 . Both integrands have a genuinely
admissible circle when Im z ≠ 0. This file concerns an individual contour.
-/

namespace ManuscriptAudit.Paper8LocalContour

open Paper8ContourGammaSeries (a differentiableOn_punctured)
open Paper8HolomorphicPartPhase (periodCoefficient qParameter qParameter_norm)
open Metric Set

noncomputable section

def root (k : ℕ) : ℂ := Complex.exp (((Real.pi / (k : ℝ) : ℝ) : ℂ) * Complex.I)

theorem root_eq_literal {k : ℕ} (hk : 0 < k) :
    root k = Complex.exp (periodCoefficient / (2 * (k : ℂ))) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  unfold root periodCoefficient
  congr 1
  push_cast
  field_simp [hkC] <;> ring

theorem root_norm (k : ℕ) : ‖root k‖ = 1 := by
  rw [root, Complex.norm_exp]
  simp [Complex.mul_re]

def factor (β : ℝ) (k : ℕ) (d : ℤ) (z s : ℂ) : ℂ :=
  root k ^ d * qParameter z * Complex.exp ((β : ℂ) * s)

def denominator (β : ℝ) (k : ℕ) (d : ℤ) (z s : ℂ) : ℂ :=
  1 - factor β k d z s

def integrand (α β : ℝ) (k : ℕ) (d : ℤ) (z s : ℂ) : ℂ :=
  a k s * Complex.exp ((α : ℂ) * s) / denominator β k d z s

def radius (z : ℂ) : ℝ := Real.pi * |z.im| / 24

def phi (α β : ℝ) (k : ℕ) (d : ℤ) (z : ℂ) : ℂ :=
  (periodCoefficient)⁻¹ * circleIntegral (integrand α β k d z) 0 (radius z)

def literalPhi (k : ℕ) (d : ℤ) (z : ℂ) : ℂ := phi (2 / 3) 16 k d z

def rhoadesPhi (k : ℕ) (d : ℤ) (z : ℂ) : ℂ := phi 23 24 k d z

theorem factor_norm (β : ℝ) (k : ℕ) (d : ℤ) (z s : ℂ) :
    ‖factor β k d z s‖ = Real.exp (-(2 * Real.pi * z.im) + β * s.re) := by
  simp only [factor, norm_mul, norm_zpow, root_norm, one_zpow, one_mul, qParameter_norm,
    Complex.norm_exp, ← Real.exp_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem denominator_ne_zero_of_small_norm {β : ℝ} (hβ : 0 < β) (k : ℕ) (d : ℤ)
    {z s : ℂ} (hs : β * ‖s‖ < 2 * Real.pi * |z.im|) : denominator β k d z s ≠ 0 := by
  intro h
  have hFactor : factor β k d z s = 1 := (sub_eq_zero.mp h).symm
  have hExp : Real.exp (-(2 * Real.pi * z.im) + β * s.re) = Real.exp 0 := by
    rw [← factor_norm β k d z s, hFactor, norm_one, Real.exp_zero]
  have hEq : β * s.re = 2 * Real.pi * z.im := by
    have he := Real.exp_injective hExp
    linarith
  have hAbs : |β * s.re| ≤ β * ‖s‖ := by
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm s) hβ.le
  rw [hEq, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hAbs
  exact (not_le_of_gt hs) hAbs

theorem radius_pos {z : ℂ} (hz : z.im ≠ 0) : 0 < radius z :=
  div_pos (mul_pos Real.pi_pos (abs_pos.mpr hz)) (by norm_num)

theorem sphere_norm_lt {z s : ℂ} (hz : z.im ≠ 0) (hs : s ∈ sphere (0 : ℂ) (radius z))
    {β : ℝ} (hβ : β ≤ 24) :
    β * ‖s‖ < 2 * Real.pi * |z.im| := by
  have hEq : ‖s‖ = radius z := by
    simpa only [mem_sphere, dist_zero_right] using hs
  calc
    _ = β * radius z := by rw [hEq]
    _ ≤ 24 * radius z := mul_le_mul_of_nonneg_right hβ (radius_pos hz).le
    _ = Real.pi * |z.im| := by unfold radius; ring
    _ < _ := by linarith [mul_pos Real.pi_pos (abs_pos.mpr hz)]

theorem integrand_continuousOn_circle {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ}
    (hz : z.im ≠ 0) (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24) :
    ContinuousOn (integrand α β k d z) (sphere (0 : ℂ) (radius z)) := by
  have ha : ContinuousOn (a k) (sphere (0 : ℂ) (radius z)) :=
    (differentiableOn_punctured hk).continuousOn.mono (fun s hs => by
      have hNorm : ‖s‖ = radius z := by
        simpa only [mem_sphere, dist_zero_right] using hs
      exact norm_pos_iff.mp (by simpa only [hNorm] using radius_pos hz))
  have hExp (t : ℝ) : Continuous (fun s : ℂ => Complex.exp ((t : ℂ) * s)) :=
    Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have hDen : Continuous (denominator β k d z) :=
    continuous_const.sub (continuous_const.mul (hExp β))
  exact (ha.mul (hExp α).continuousOn).div hDen.continuousOn
    (fun _ hs => denominator_ne_zero_of_small_norm hβ k d (sphere_norm_lt hz hs hβ'))

theorem literalCircleIntegrable {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ} (hz : z.im ≠ 0) :
    CircleIntegrable (integrand (2 / 3) 16 k d z) 0 (radius z) :=
  (integrand_continuousOn_circle hk d hz (2 / 3) (β := 16) (by norm_num) (by norm_num))
    |>.circleIntegrable (radius_pos hz).le

theorem rhoadesCircleIntegrable {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ} (hz : z.im ≠ 0) :
    CircleIntegrable (integrand 23 24 k d z) 0 (radius z) :=
  (integrand_continuousOn_circle hk d hz 23 (β := 24) (by norm_num) le_rfl)
    |>.circleIntegrable (radius_pos hz).le

end
end ManuscriptAudit.Paper8LocalContour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LocalContour.root_eq_literal,
      ``ManuscriptAudit.Paper8LocalContour.factor_norm,
      ``ManuscriptAudit.Paper8LocalContour.denominator_ne_zero_of_small_norm,
      ``ManuscriptAudit.Paper8LocalContour.radius_pos,
      ``ManuscriptAudit.Paper8LocalContour.integrand_continuousOn_circle,
      ``ManuscriptAudit.Paper8LocalContour.literalCircleIntegrable,
      ``ManuscriptAudit.Paper8LocalContour.rhoadesCircleIntegrable] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
