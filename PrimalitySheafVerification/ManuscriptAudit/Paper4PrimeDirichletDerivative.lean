import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.LSeries.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper4PrimeLogWeightPole

/-! The literal prime Dirichlet series in an invertible residue class has
derivative the negative of its actual logarithm-weighted prime series. -/

namespace ManuscriptAudit.Paper4PrimeDirichletDerivative

open ArithmeticFunction ArithmeticFunction.vonMangoldt LSeries
open Paper4MangoldtPole Paper4PrimeLogWeightPole

noncomputable section

variable {q : ℕ} [NeZero q] (a : ZMod q)

def countCoeff (n : ℕ) : ℝ := if n.Prime ∧ (n : ZMod q) = a then 1 else 0

abbrev complexCoeff (n : ℕ) : ℂ := countCoeff a n

def primeDirichletSeries (s : ℝ) : ℝ := (LSeries (complexCoeff a) (s : ℂ)).re

private theorem countCoeff_zero : countCoeff a 0 = 0 := by simp [countCoeff]

private theorem abscissa_le : abscissaOfAbsConv (complexCoeff a) ≤ 1 := by
  apply (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1))
  intro s hs
  apply LSeriesSummable_of_bounded_of_one_lt_real (m := 1) _ hs
  intro n _
  change ‖(countCoeff a n : ℂ)‖ ≤ 1
  unfold countCoeff
  split_ifs <;> norm_num

theorem primeTerm_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n ↦ countCoeff a n / (n : ℝ) ^ s) :=
  summable_real_of_abscissaOfAbsConv_lt ((abscissa_le a).trans_lt (by exact_mod_cast hs))

theorem series_eq_tsum {s : ℝ} (hs : 1 < s) :
    primeDirichletSeries a s = ∑' n, countCoeff a n / (n : ℝ) ^ s :=
  real_part_eq_tsum (countCoeff_zero a) s
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissa_le a).trans_lt (by exact_mod_cast hs)))

private theorem logMul_eq_real (n : ℕ) :
    logMul (complexCoeff a) n = ((if n.Prime then residueClass a n else 0 : ℝ) : ℂ) := by
  by_cases hp : n.Prime
  · by_cases hEq : (n : ZMod q) = a
    · simp only [logMul, complexCoeff, countCoeff, hp, hEq, and_self, if_true,
        Complex.ofReal_one, mul_one, residueClass, Set.indicator_of_mem,
        Set.mem_setOf_eq, vonMangoldt_apply_prime hp]
      exact Complex.natCast_log.symm
    · simp [logMul, complexCoeff, countCoeff, hp, hEq, residueClass]
  · simp [logMul, complexCoeff, countCoeff, hp]

/-- An exact derivative of the actual real prime Dirichlet series. -/
theorem hasDerivAt_primeDirichletSeries {s : ℝ} (hs : 1 < s) :
    HasDerivAt (primeDirichletSeries a) (-(primeSeries a s)) s := by
  have hs' : abscissaOfAbsConv (complexCoeff a) < (s : ℂ).re :=
    (abscissa_le a).trans_lt (by exact_mod_cast hs)
  have hD := (LSeries_hasDerivAt hs').real_of_complex
  have hEq : logMul (complexCoeff a) = fun n ↦
      ((if n.Prime then residueClass a n else 0 : ℝ) : ℂ) :=
    funext (logMul_eq_real a)
  have hSum := LSeriesSummable_logMul_of_lt_re hs'
  rw [hEq] at hSum hD
  have hWeighted :
      (LSeries (fun n ↦ ((if n.Prime then residueClass a n else 0 : ℝ) : ℂ)) (s : ℂ)).re =
        primeSeries a s := by
    exact real_part_eq_tsum (by simp) s hSum
  rw [Complex.neg_re, hWeighted] at hD
  exact hD

end
end ManuscriptAudit.Paper4PrimeDirichletDerivative

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4PrimeDirichletDerivative.series_eq_tsum,
      ``ManuscriptAudit.Paper4PrimeDirichletDerivative.hasDerivAt_primeDirichletSeries] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
