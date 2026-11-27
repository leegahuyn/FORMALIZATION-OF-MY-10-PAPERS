import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The logarithmic zero-mode form for the printed cusp operator. -/

namespace ManuscriptAudit.Paper9LogQuadratic

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

def modeDensity (g g'' : ℝ → ℂ) (t : ℝ) : ℝ :=
  ((star (g t)) * (g'' t - (1 / 4 : ℂ) * g t)).re

theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ (2 : ℕ) := by
  change (conj z * z).re = _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.normSq_apply]

theorem re_ofReal_mul (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

theorem modeDensity_eq (g g'' : ℝ → ℂ) (t : ℝ) :
    modeDensity g g'' t =
      (star (g t) * g'' t).re - (1 / 4 : ℝ) * ‖g t‖ ^ (2 : ℕ) := by
  unfold modeDensity
  rw [mul_sub, Complex.sub_re, mul_left_comm (star (g t)) (1 / 4 : ℂ),
    show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
    re_ofReal_mul, re_star_mul_self]

theorem mode_form_eq (g g' g'' : ℝ → ℂ) (a b : ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hg'' : Continuous g'') (ha : g a = 0) (hb : g b = 0) :
    (∫ t in a..b, modeDensity g g'' t) =
      -(∫ t in a..b, ‖g' t‖ ^ (2 : ℕ)) - (1 / 4 : ℝ) * ∫ t in a..b, ‖g t‖ ^ (2 : ℕ) := by
  let flux : ℝ → ℝ := fun t => (star (g t) * g' t).re
  have hFlux (t : ℝ) :
      HasDerivAt flux (‖g' t‖ ^ (2 : ℕ) + (star (g t) * g'' t).re) t := by
    have hc : HasDerivAt (fun t => star (g t)) (star (g' t)) t :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt (hg t)
    have hm := hc.mul (hg' t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt hm
    change HasDerivAt flux ((star (g' t) * g' t + star (g t) * g'' t).re) t at h
    rwa [Complex.add_re, re_star_mul_self] at h
  have hG : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hG' : Continuous g' := continuous_iff_continuousAt.mpr (fun t => (hg' t).continuousAt)
  have hCG : Continuous (fun t => star (g t)) := Complex.conjCLE.continuous.comp hG
  have hA : IntervalIntegrable (fun t => ‖g' t‖ ^ (2 : ℕ)) volume a b :=
    (hG'.norm.pow 2).intervalIntegrable a b
  have hB : IntervalIntegrable (fun t => (star (g t) * g'' t).re) volume a b :=
    (Complex.continuous_re.comp (hCG.mul hg'')).intervalIntegrable a b
  have hC : IntervalIntegrable (fun t => (1 / 4 : ℝ) * ‖g t‖ ^ (2 : ℕ)) volume a b :=
    (continuous_const.mul (hG.norm.pow 2)).intervalIntegrable a b
  have hSum : (∫ t in a..b, ‖g' t‖ ^ (2 : ℕ)) +
      (∫ t in a..b, (star (g t) * g'' t).re) = 0 := by
    rw [← intervalIntegral.integral_add hA hB,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFlux t) (hA.add hB)]
    simp [flux, ha, hb]
  simp_rw [modeDensity_eq]
  rw [intervalIntegral.integral_sub hB hC, intervalIntegral.integral_const_mul]
  linarith only [hSum]

theorem mode_form_nonpositive (g g' g'' : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hg'' : Continuous g'') (ha : g a = 0) (hb : g b = 0) :
    (∫ t in a..b, modeDensity g g'' t) ≤ 0 := by
  rw [mode_form_eq g g' g'' a b hg hg' hg'' ha hb]
  have hA : 0 ≤ ∫ t in a..b, ‖g' t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ∫ t in a..b, ‖g t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  linarith only [hA, hB]

end
end ManuscriptAudit.Paper9LogQuadratic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9LogQuadratic.modeDensity_eq,
      ``ManuscriptAudit.Paper9LogQuadratic.mode_form_eq,
      ``ManuscriptAudit.Paper9LogQuadratic.mode_form_nonpositive] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
