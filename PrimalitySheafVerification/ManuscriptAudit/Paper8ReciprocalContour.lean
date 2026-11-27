import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8LocalContour

/-!
# The inverse-nome form of the lower-half-plane contour

Physical p. 335 uses β=16 and α=2/3, so the reciprocal kernel has
exponential α-β=-46/3. In Rhoades, Theorem 1.1 and (3.2)
(https://arxiv.org/pdf/1111.1495), the corresponding value is -1.
These are exact identities for the individual circle integrals.
-/

namespace ManuscriptAudit.Paper8ReciprocalContour

open Metric Set
open Paper8ContourGammaSeries (a)
open Paper8HolomorphicPartPhase (qParameter periodCoefficient)
open Paper8LocalContour
  (root factor factor_norm denominator denominator_ne_zero_of_small_norm integrand phi radius
    radius_pos sphere_norm_lt literalPhi rhoadesPhi)

noncomputable section

theorem qParameter_neg (z : ℂ) : qParameter (-z) = (qParameter z)⁻¹ := by
  rw [qParameter, qParameter, mul_neg, Complex.exp_neg]

theorem factor_mul_reciprocal (β : ℝ) (k : ℕ) (d : ℤ) (z s : ℂ) :
    factor β k d z s * factor (-β) k (-d) (-z) s = 1 := by
  have hr : root k ^ d ≠ 0 := zpow_ne_zero d (Complex.exp_ne_zero _)
  have hq : qParameter z ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp ((β : ℂ) * s) ≠ 0 := Complex.exp_ne_zero _
  unfold factor
  rw [zpow_neg, qParameter_neg, Complex.ofReal_neg, neg_mul, Complex.exp_neg]
  field_simp [hr, hq, he] <;> ring

private theorem reciprocal_div {F G A : ℂ} (h : F * G = 1) (hF : 1 - F ≠ 0) :
    F * (A / (1 - F)) = -(A / (1 - G)) := by
  have hG : 1 - G ≠ 0 := by
    intro h0
    have hg : G = 1 := (sub_eq_zero.mp h0).symm
    rw [hg, mul_one] at h
    exact hF (sub_eq_zero.mpr h.symm)
  calc
    _ = (A * F) / (1 - F) := by ring
    _ = (-A) / (1 - G) := by
      apply (div_eq_div_iff hF hG).2
      calc
        _ = A * (F - F * G) := by ring
        _ = _ := by rw [h]; ring
    _ = _ := neg_div _ _

theorem integrand_reciprocal (α : ℝ) {β : ℝ} (hβ : 0 < β) (k : ℕ) (d : ℤ)
    {z s : ℂ} (hs : β * ‖s‖ < 2 * Real.pi * |z.im|) :
    (root k ^ d * qParameter z) * integrand α β k d z s =
      -integrand (α - β) (-β) k (-d) (-z) s := by
  have hDen : 1 - factor β k d z s ≠ 0 :=
    denominator_ne_zero_of_small_norm hβ k d hs
  have hExp : Complex.exp ((α : ℂ) * s) =
      Complex.exp (((α - β : ℝ) : ℂ) * s) * Complex.exp ((β : ℂ) * s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = factor β k d z s *
      ((a k s * Complex.exp (((α - β : ℝ) : ℂ) * s)) / (1 - factor β k d z s)) := by
      rw [integrand, denominator, hExp]
      unfold factor
      ring
    _ = _ := reciprocal_div (factor_mul_reciprocal β k d z s) hDen

theorem phi_reciprocal (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (k : ℕ) (d : ℤ) {z : ℂ} (hz : z.im ≠ 0) :
    (root k ^ d * qParameter z) * phi α β k d z =
      -phi (α - β) (-β) k (-d) (-z) := by
  have hRadius : radius (-z) = radius z := by simp [radius, Complex.neg_im]
  unfold phi
  rw [hRadius]
  calc
    _ = periodCoefficient⁻¹ * circleIntegral
        (fun s => (root k ^ d * qParameter z) * integrand α β k d z s) 0 (radius z) := by
      rw [circleIntegral.integral_const_mul]
      ring
    _ = periodCoefficient⁻¹ * circleIntegral
        (fun s => -integrand (α - β) (-β) k (-d) (-z) s) 0 (radius z) := by
      apply congrArg (periodCoefficient⁻¹ * ·)
      apply circleIntegral.integral_congr (radius_pos hz).le
      intro s hs
      exact integrand_reciprocal α hβ k d (sphere_norm_lt hz hs hβ')
    _ = _ := by
      have hNeg : (fun s => -integrand (α - β) (-β) k (-d) (-z) s) =
          (fun s => (-1 : ℂ) * integrand (α - β) (-β) k (-d) (-z) s) := by
        funext s
        simp only [neg_one_mul]
      rw [hNeg, circleIntegral.integral_const_mul]
      ring

theorem literalPhi_reciprocal (k : ℕ) (d : ℤ) {z : ℂ} (hz : z.im < 0) :
    (root k ^ d * qParameter z) * literalPhi k d z =
      -phi (-46 / 3) (-16) k (-d) (-z) := by
  have h := phi_reciprocal (2 / 3) (β := 16) (by norm_num) (by norm_num) k d hz.ne
  change _ * phi (2 / 3) 16 k d z = _
  have hα : (2 / 3 : ℝ) - 16 = -46 / 3 := by norm_num
  rw [hα] at h
  exact h

theorem rhoadesPhi_reciprocal (k : ℕ) (d : ℤ) {z : ℂ} (hz : z.im < 0) :
    (root k ^ d * qParameter z) * rhoadesPhi k d z =
      -phi (-1) (-24) k (-d) (-z) := by
  have h := phi_reciprocal 23 (β := 24) (by norm_num) le_rfl k d hz.ne
  change _ * phi 23 24 k d z = _
  have hα : (23 : ℝ) - 24 = -1 := by norm_num
  rw [hα] at h
  exact h

theorem reciprocal_factor_norm_lt_one {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    (k : ℕ) (d : ℤ) {z s : ℂ} (hz : z.im < 0) (hs : s ∈ sphere (0 : ℂ) (radius z)) :
    ‖factor (-β) k (-d) (-z) s‖ < 1 := by
  rw [factor_norm, Complex.neg_im, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hNorm := sphere_norm_lt hz.ne hs hβ'
  have hRe := mul_le_mul_of_nonneg_left ((abs_le.mp (Complex.abs_re_le_norm s)).1) hβ.le
  rw [abs_of_neg hz] at hNorm
  linarith

end
end ManuscriptAudit.Paper8ReciprocalContour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalContour.qParameter_neg,
      ``ManuscriptAudit.Paper8ReciprocalContour.factor_mul_reciprocal,
      ``ManuscriptAudit.Paper8ReciprocalContour.integrand_reciprocal,
      ``ManuscriptAudit.Paper8ReciprocalContour.phi_reciprocal,
      ``ManuscriptAudit.Paper8ReciprocalContour.literalPhi_reciprocal,
      ``ManuscriptAudit.Paper8ReciprocalContour.rhoadesPhi_reciprocal,
      ``ManuscriptAudit.Paper8ReciprocalContour.reciprocal_factor_norm_lt_one] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
