import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! On the real half-line the actual von Mangoldt L-series of a reduced
residue class has a bounded error after its polar term is removed. -/

namespace ManuscriptAudit.Paper4MangoldtPole

open ArithmeticFunction.vonMangoldt LSeries
open scoped LSeries.notation

noncomputable section

variable {q : ℕ} [NeZero q] (a : ZMod q)

def realSeries (s : ℝ) : ℝ := ∑' n, residueClass a n / (n : ℝ) ^ s

theorem realSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ s) := by
  exact summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hs))

/-- Real coefficients of an absolutely convergent native L-series give
the literal real Dirichlet sum on the real axis. -/
theorem real_part_eq_tsum {f : ℕ → ℝ} (h₀ : f 0 = 0) (s : ℝ)
    (hSum : LSeriesSummable (fun n ↦ (f n : ℂ)) (s : ℂ)) :
    (LSeries (fun n ↦ (f n : ℂ)) (s : ℂ)).re = ∑' n, f n / (n : ℝ) ^ s := by
  rw [LSeries, Complex.re_tsum hSum]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, h₀]
  · simp only [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_div, Complex.ofReal_re]

private theorem complexSeries_re {s : ℝ} (hs : 1 < s) :
    (LSeries (fun n ↦ (residueClass a n : ℂ)) (s : ℂ)).re = realSeries a s := by
  exact real_part_eq_tsum (residueClass_apply_zero a) s
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hs)))

/-- The real error is the real part of the actual holomorphic continuation. -/
theorem realSeries_sub_pole {s : ℝ} (ha : IsUnit a) (hs : 1 < s) :
    realSeries a s - (q.totient : ℝ)⁻¹ / (s - 1) = (LFunctionResidueClassAux a s).re := by
  have h := eqOn_LFunctionResidueClassAux ha
    (show (s : ℂ) ∈ {z : ℂ | 1 < z.re} by simpa using hs)
  have hCast : (q.totient : ℂ)⁻¹ / ((s : ℂ) - 1) =
      (((q.totient : ℝ)⁻¹ / (s - 1) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_natCast, Complex.ofReal_one]
  change LFunctionResidueClassAux a (s : ℂ) =
    LSeries (fun n ↦ (residueClass a n : ℂ)) (s : ℂ) -
      (q.totient : ℂ)⁻¹ / ((s : ℂ) - 1) at h
  rw [hCast] at h
  have hRe := congrArg Complex.re h
  rw [Complex.sub_re, complexSeries_re a hs, Complex.ofReal_re] at hRe
  exact hRe.symm

theorem bounded_real_pole_error (ha : IsUnit a) :
    ∃ B : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      |realSeries a s - (q.totient : ℝ)⁻¹ / (s - 1)| ≤ B := by
  have hc : ContinuousOn (fun s : ℝ ↦ (LFunctionResidueClassAux a s).re) (Set.Icc 1 2) :=
    Complex.continuous_re.continuousOn.comp (t := Set.univ)
      (continuousOn_LFunctionResidueClassAux a) (fun ⦃_⦄ _ ↦ trivial)
      |>.comp Complex.continuous_ofReal.continuousOn (fun s hs ↦ by
        simpa only [Set.mem_setOf_eq, Complex.ofReal_re] using hs.1)
  obtain ⟨B, hB⟩ := bddAbove_def.mp (IsCompact.bddAbove_image isCompact_Icc hc.abs)
  refine ⟨B, fun s hs ↦ ?_⟩
  rw [realSeries_sub_pole a ha hs.1]
  exact hB _ (Set.mem_image_of_mem _ (Set.mem_Icc_of_Ioc hs))

end
end ManuscriptAudit.Paper4MangoldtPole

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4MangoldtPole.realSeries_summable,
      ``ManuscriptAudit.Paper4MangoldtPole.realSeries_sub_pole,
      ``ManuscriptAudit.Paper4MangoldtPole.bounded_real_pole_error] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
