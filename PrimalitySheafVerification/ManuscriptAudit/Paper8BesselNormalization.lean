import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import PrimalitySheafVerification.ManuscriptAudit.PrintedRademacherTail

/-!
# Modified Bessel I of order one half

The first-kind function is defined by the gamma series on positive real
arguments, as in DLMF (10.25.2). Gamma recurrence and the sinh sum give
the elementary evaluation DLMF (10.39.1). The manuscript uses a different
constant in its elementary expression.
-/

namespace ManuscriptAudit.Paper8BesselNormalization

open PrintedRademacherTail

noncomputable section

def gammaWeight (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * Real.Gamma ((n : ℝ) + 3 / 2)

theorem gammaWeight_eq (n : ℕ) :
    gammaWeight n = Real.sqrt Real.pi * ((2 * n + 1).factorial : ℝ) / 2 ^ (2 * n + 1) := by
  induction n with
  | zero =>
    change 1 * Real.Gamma ((0 : ℝ) + 3 / 2) = Real.sqrt Real.pi * 1 / 2 ^ (1 : ℕ)
    rw [show (0 : ℝ) + 3 / 2 = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  | succ n h =>
    have hIndex : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    calc
      gammaWeight (n + 1) =
          ((n : ℝ) + 1) * ((n : ℝ) + 3 / 2) * gammaWeight n := by
        simp only [gammaWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
        rw [show (n : ℝ) + 1 + 3 / 2 = ((n : ℝ) + 3 / 2) + 1 by ring,
          Real.Gamma_add_one (by positivity)]
        ring
      _ = Real.sqrt Real.pi * ((2 * (n + 1) + 1).factorial : ℝ) /
          2 ^ (2 * (n + 1) + 1) := by
        rw [h, hIndex, Nat.factorial_succ ((2 * n + 1) + 1), Nat.factorial_succ (2 * n + 1),
          pow_add]
        push_cast
        field_simp <;> ring

private theorem series_term_eq (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (x / 2) ^ (2 * n) / gammaWeight n =
      (2 / (Real.sqrt Real.pi * x)) * (x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : ((2 * n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hTwo : (2 : ℝ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [gammaWeight_eq, div_pow, pow_succ (2 : ℝ) (2 * n), pow_succ x (2 * n)]
  field_simp [hπ, hf, hx.ne', hTwo] <;> ring

def halfBessel (x : ℝ) : ℝ :=
  Real.sqrt (x / 2) * ∑' n : ℕ, (x / 2) ^ (2 * n) / gammaWeight n

private theorem standard_factor (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x / 2) * (2 / (Real.sqrt Real.pi * x)) = Real.sqrt (2 / (Real.pi * x)) := by
  have hSq : (Real.sqrt (x / 2) * (2 / (Real.sqrt Real.pi * x))) ^ 2 =
      2 / (Real.pi * x) := by
    simp only [mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ x / 2),
      Real.sq_sqrt Real.pi_pos.le]
    field_simp [Real.pi_pos.ne', hx.ne'] <;> ring
  rw [← hSq, Real.sqrt_sq (by positivity)]

theorem halfBessel_eq (x : ℝ) (hx : 0 < x) :
    halfBessel x = Real.sqrt (2 / (Real.pi * x)) * Real.sinh x := by
  have hs := ((Real.hasSum_sinh x).mul_left (2 / (Real.sqrt Real.pi * x))).congr
    (fun n => (series_term_eq x hx n).symm)
  rw [halfBessel, hs.tsum_eq, ← mul_assoc, standard_factor x hx]

theorem printedBessel_eq_pi_over_two_mul_halfBessel (x : ℝ) (hx : 0 < x) :
    printedBessel x = (Real.pi / 2) * halfBessel x := by
  have hs : ((Real.pi / 2) * Real.sqrt (2 / (Real.pi * x))) ^ 2 =
      Real.pi / (2 * x) := by
    simp only [mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / (Real.pi * x))]
    field_simp [Real.pi_pos.ne', hx.ne'] <;> ring
  have hf : Real.sqrt (Real.pi / (2 * x)) =
      (Real.pi / 2) * Real.sqrt (2 / (Real.pi * x)) := by
    rw [← hs, Real.sqrt_sq (by positivity)]
  rw [printedBessel, halfBessel_eq x hx, hf, mul_assoc]

theorem halfBessel_lt_printedBessel (x : ℝ) (hx : 0 < x) :
    halfBessel x < printedBessel x := by
  have hB : 0 < halfBessel x := by
    rw [halfBessel_eq x hx]
    exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sinh_pos_iff.mpr hx)
  rw [printedBessel_eq_pi_over_two_mul_halfBessel x hx]
  exact (one_mul (halfBessel x)).symm.trans_lt
    (mul_lt_mul_of_pos_right (by linarith [Real.pi_gt_three]) hB)

theorem standard_rademacher_tail_majorant_not_summable
    (ell n K : ℕ) (hell : 0 < ell) (hn : 0 < n) :
    ¬ Summable (fun j : ℕ =>
      (divisorWeight ell n (j + (K + 1)) /
        Real.sqrt (↑(j + (K + 1)) : ℝ)) *
      halfBessel (4 * Real.pi * Real.sqrt ((ell : ℝ) * (n : ℝ)) /
        (↑(j + (K + 1)) : ℝ))) := by
  intro h
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply paper8_printed_rademacher_tail_majorant_not_summable ell n K hell hn
  refine (h.mul_left (Real.pi / 2)).congr fun j => ?_
  have hc : (0 : ℝ) < (↑(j + (K + 1)) : ℝ) := by positivity
  have hb : 0 < 4 * Real.pi * Real.sqrt ((ell : ℝ) * (n : ℝ)) /
      (↑(j + (K + 1)) : ℝ) := by positivity
  rw [printedBessel_eq_pi_over_two_mul_halfBessel _ hb]
  ring

end
end ManuscriptAudit.Paper8BesselNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8BesselNormalization.gammaWeight_eq,
      ``ManuscriptAudit.Paper8BesselNormalization.halfBessel_eq,
      ``ManuscriptAudit.Paper8BesselNormalization.printedBessel_eq_pi_over_two_mul_halfBessel,
      ``ManuscriptAudit.Paper8BesselNormalization.halfBessel_lt_printedBessel,
      ``ManuscriptAudit.Paper8BesselNormalization.standard_rademacher_tail_majorant_not_summable] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
