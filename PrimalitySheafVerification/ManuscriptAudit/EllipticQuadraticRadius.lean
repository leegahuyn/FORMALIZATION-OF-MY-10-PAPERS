import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The precise elliptic quadratic circle comparison in Paper 7

The roots of the literal polynomial 1 − aT + pT² are on the circle
of radius 1/√p exactly when |a| ≤ 2√p, for p>0 and real a. This
part of the manuscript is an exact quadratic statement, independent
of any global Euler product identification.
-/

namespace ManuscriptAudit.EllipticQuadraticRadius

open Polynomial

noncomputable section

def localPolynomial (p a : ℝ) : ℂ[X] :=
  1 - C (a : ℂ) * X + C (p : ℂ) * X ^ 2

private abbrev expression (p a : ℝ) (z : ℂ) : ℂ := 1 - (a : ℂ) * z + (p : ℂ) * z ^ 2

private theorem eval_localPolynomial (p a : ℝ) (z : ℂ) :
    (localPolynomial p a).eval z = expression p a z := by
  simp [localPolynomial, expression]

private theorem radius_of_weighted_norm (p : ℝ) (hp : 0 < p) (z : ℂ)
    (h : p * Complex.normSq z = 1) : ‖z‖ = 1 / Real.sqrt p := by
  let r := 1 / Real.sqrt p
  have hr : 0 < r := one_div_pos.mpr (Real.sqrt_pos.2 hp)
  have hrSq : p * r ^ 2 = 1 := by
    change p * (1 / Real.sqrt p) ^ 2 = 1
    rw [div_pow, one_pow, Real.sq_sqrt hp.le, one_div]
    exact mul_inv_cancel₀ hp.ne'
  have hEq : ‖z‖ ^ 2 = r ^ 2 := by
    apply mul_left_cancel₀ hp.ne'
    rw [Complex.sq_norm, h, hrSq]
  have hFactor : (‖z‖ - r) * (‖z‖ + r) = 0 := by linear_combination hEq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hFactor).resolve_right
    (ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) hr)))

private theorem radius_of_hasse (p a : ℝ) (hp : 0 < p)
    (ha : |a| ≤ 2 * Real.sqrt p) (z : ℂ) (hz : expression p a z = 0) :
    ‖z‖ = 1 / Real.sqrt p := by
  have haSq : a ^ 2 ≤ 4 * p := by
    calc
      a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      _ ≤ (2 * Real.sqrt p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ = _ := by linear_combination 4 * Real.sq_sqrt hp.le
  have hRe : 1 - a * z.re + p * (z.re ^ 2 - z.im ^ 2) = 0 := by
    have h := congrArg Complex.re hz
    simp [expression, pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im] at h
    linear_combination h
  have hIm : z.im * (2 * p * z.re - a) = 0 := by
    have h := congrArg Complex.im hz
    simp [expression, pow_two, Complex.add_im, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h
    linear_combination h
  have he : 2 * p * z.re - a = 0 := by
    rcases mul_eq_zero.mp hIm with hi | he
    · rw [hi] at hRe
      have hD : (2 * p * z.re - a) ^ 2 = a ^ 2 - 4 * p := by
        linear_combination (4 * p) * hRe
      have hZero : (2 * p * z.re - a) ^ 2 = 0 :=
        le_antisymm (hD.le.trans (sub_nonpos.mpr haSq)) (sq_nonneg _)
      exact pow_eq_zero hZero
    · exact he
  apply radius_of_weighted_norm p hp z
  rw [Complex.normSq_apply]
  have hA : a = 2 * p * z.re := (sub_eq_zero.mp he).symm
  rw [hA] at hRe
  linear_combination -hRe

private theorem exists_root (p a : ℝ) (hp : 0 < p) :
    ∃ z : ℂ, expression p a z = 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℂ) ^ 2 - 4 * (p : ℂ))
    (n := 2) (by decide)
  let z : ℂ := ((a : ℂ) + w) / (2 * (p : ℂ))
  refine ⟨z, ?_⟩
  calc
    expression p a z = (4 * (p : ℂ) - (a : ℂ) ^ 2 + w ^ 2) / (4 * (p : ℂ)) := by
      dsimp only [expression, z]
      field_simp [hpC] <;> ring
    _ = 0 := by
      rw [hw, show 4 * (p : ℂ) - (a : ℂ) ^ 2 + ((a : ℂ) ^ 2 - 4 * (p : ℂ)) = 0 by ring,
        zero_div]

/-- The stated Hasse discriminant bound is equivalent to the literal reciprocal radius. -/
theorem all_roots_radius_iff (p a : ℝ) (hp : 0 < p) :
    (∀ z : ℂ, (localPolynomial p a).IsRoot z → ‖z‖ = 1 / Real.sqrt p) ↔
      |a| ≤ 2 * Real.sqrt p := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_root p a hp
    have hr := h z (by change (localPolynomial p a).eval z = 0; rw [eval_localPolynomial]; exact hz)
    have hz₀ : z ≠ 0 := by
      intro he
      subst z
      simpa [expression] using hz
    have ha : (a : ℂ) = z⁻¹ + (p : ℂ) * z := by
      field_simp [hz₀]
      linear_combination -hz
    have hs := Real.sqrt_pos.2 hp
    calc
      |a| = ‖(a : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖z⁻¹ + (p : ℂ) * z‖ := by rw [ha]
      _ ≤ ‖z‖⁻¹ + p * ‖z‖ := by
        simpa only [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le] using
          norm_add_le z⁻¹ ((p : ℂ) * z)
      _ = 2 * Real.sqrt p := by
        rw [hr, one_div, inv_inv]
        field_simp [hs.ne'] <;> nlinarith [Real.sq_sqrt hp.le]
  · intro ha z hz
    apply radius_of_hasse p a hp ha z
    change (localPolynomial p a).eval z = 0 at hz
    rwa [eval_localPolynomial] at hz

end

end ManuscriptAudit.EllipticQuadraticRadius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.EllipticQuadraticRadius.all_roots_radius_iff
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
