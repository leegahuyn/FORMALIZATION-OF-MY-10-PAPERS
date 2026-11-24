import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The printed double numerator in Paper 8 G.1

Physical PDF p. 350 defines the exponent with an m²/2 term. The second index
below runs through m=k+1 with k natural. At τ=i the q-power has the
nonnegative real value exp(−2πE). In either summation order the inner
families are summable and the outer sum diverges.

This file treats the p. 350 double numerator. The p. 305 bilateral Appell
numerator and the p. 350 theta denominator are separate calculations.
-/

namespace ManuscriptAudit.AppellDoubleRidge

noncomputable def doubleExponent (n m : ℤ) : ℝ :=
  (n : ℝ) ^ 2 / 2 + (n : ℝ) * (1 + (m : ℝ)) + (m : ℝ) ^ 2 / 2

noncomputable def doubleTerm (τ : ℂ) (n m : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ * (doubleExponent n m : ℂ))

noncomputable def doubleTermRealAtI (n m : ℤ) : ℝ :=
  Real.exp (-2 * Real.pi * doubleExponent n m)

theorem doubleExponent_ridge (m : ℤ) :
    doubleExponent (-m - 1) m = -(m : ℝ) - 1 / 2 := by
  simp only [doubleExponent, Int.cast_sub, Int.cast_neg, Int.cast_one]
  ring

theorem doubleTerm_at_I (n m : ℤ) :
    doubleTerm Complex.I n m = (doubleTermRealAtI n m : ℂ) := by
  rw [doubleTerm, doubleTermRealAtI, Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  calc
    _ = (2 * (Real.pi : ℂ) * (doubleExponent n m : ℂ)) * (Complex.I * Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

private theorem one_le_doubleTermRealAtI_ridge (m : ℤ) (hm : 0 ≤ m) :
    1 ≤ doubleTermRealAtI (-m - 1) m := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [doubleTermRealAtI, Real.one_le_exp_iff, doubleExponent_ridge]
  rw [show -2 * Real.pi * (-(m : ℝ) - 1 / 2) =
    2 * Real.pi * ((m : ℝ) + 1 / 2) by ring]
  positivity

private theorem not_summable_of_one_le {f : ℕ → ℝ} (hf : ∀ k, 1 ≤ f k) :
    ¬ Summable f := by
  intro h
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) :=
    h.of_nonneg_of_le (fun _ => zero_le_one) hf
  exact one_ne_zero ((summable_const_iff (β := ℕ) (1 : ℝ)).1 hone)

set_option maxHeartbeats 1000000 in
private theorem not_summable_joint_real :
    ¬ Summable (fun p : ℤ × ℕ => doubleTermRealAtI p.1 ((p.2 : ℤ) + 1)) := by
  let terms : ℤ × ℕ → ℝ := fun p => doubleTermRealAtI p.1 ((p.2 : ℤ) + 1)
  change ¬ Summable terms
  intro h
  let ridge : ℕ → ℤ × ℕ := fun k => (-((k : ℤ) + 1) - 1, k)
  have hinj : Function.Injective ridge := fun _ _ hk => congrArg Prod.snd hk
  have hRidge : Summable (terms ∘ ridge) := h.comp_injective hinj
  have hlarge (k : ℕ) : 1 ≤ (terms ∘ ridge) k := by
    change 1 ≤ doubleTermRealAtI (-((k : ℤ) + 1) - 1) ((k : ℤ) + 1)
    exact one_le_doubleTermRealAtI_ridge ((k : ℤ) + 1) (by omega)
  exact not_summable_of_one_le hlarge hRidge

/-- The literal complex numerator terms have no jointly indexed sum at τ=i. -/
theorem not_summable_joint_at_I :
    ¬ Summable (fun p : ℤ × ℕ => doubleTerm Complex.I p.1 ((p.2 : ℤ) + 1)) := by
  intro h
  apply not_summable_joint_real
  simpa only [doubleTerm_at_I, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.summable h

private theorem exp_completedSquare_summable {ι : Type*}
    (c : ℝ) (f : ι → ℤ) (hf : Function.Injective f) :
    Summable (fun i => Real.exp (-2 * Real.pi * ((f i : ℝ) ^ 2 / 2 + c))) := by
  have hGauss : Summable (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] using
      summable_pow_mul_jacobiTheta₂_term_bound 0 (T := 1) zero_lt_one 0
  have hProduct : Summable (fun i =>
      Real.exp (-2 * Real.pi * c) * Real.exp (-Real.pi * (f i : ℝ) ^ 2)) :=
    (hGauss.comp_injective hf).mul_left _
  have heq : (fun i => Real.exp (-2 * Real.pi * ((f i : ℝ) ^ 2 / 2 + c))) =
      (fun i => Real.exp (-2 * Real.pi * c) * Real.exp (-Real.pi * (f i : ℝ) ^ 2)) := by
    funext i
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hProduct

private theorem summable_real_row (n : ℤ) :
    Summable (fun k : ℕ => doubleTermRealAtI n ((k : ℤ) + 1)) := by
  have exponent (m : ℤ) : doubleExponent n m = ((n : ℝ) + (m : ℝ)) ^ 2 / 2 + (n : ℝ) := by
    unfold doubleExponent
    ring
  have hinj : Function.Injective (fun k : ℕ => n + ((k : ℤ) + 1)) := by
    intro a b hab
    change n + ((a : ℤ) + 1) = n + ((b : ℤ) + 1) at hab
    exact Int.ofNat_inj.mp (add_right_cancel (add_left_cancel hab))
  have h := exp_completedSquare_summable (n : ℝ) (fun k : ℕ => n + ((k : ℤ) + 1)) hinj
  simpa only [doubleTermRealAtI, exponent, Int.cast_add] using h

private theorem summable_real_column (m : ℤ) :
    Summable (fun n : ℤ => doubleTermRealAtI n m) := by
  have exponent (n : ℤ) : doubleExponent n m =
      ((n : ℝ) + (m : ℝ) + 1) ^ 2 / 2 + (-(m : ℝ) - 1 / 2) := by
    unfold doubleExponent
    ring
  have hinj : Function.Injective (fun n : ℤ => n + m + 1) := by
    intro a b hab
    change a + m + 1 = b + m + 1 at hab
    exact add_right_cancel (add_right_cancel hab)
  have h := exp_completedSquare_summable (-(m : ℝ) - 1 / 2) (fun n : ℤ => n + m + 1) hinj
  simpa only [doubleTermRealAtI, exponent, Int.cast_add, Int.cast_one] using h

private theorem tsum_at_I_eq_real {ι : Type*} (a b : ι → ℤ)
    (h : Summable (fun i => doubleTermRealAtI (a i) (b i))) :
    (∑' i, doubleTerm Complex.I (a i) (b i)) =
      Complex.ofReal (∑' i, doubleTermRealAtI (a i) (b i)) := by
  symm
  simpa only [doubleTerm_at_I, Complex.ofRealCLM_apply] using Complex.ofRealCLM.map_tsum h

set_option maxHeartbeats 1000000 in
/-- In the printed order, m is summed first for each n. The outer sum diverges. -/
theorem not_summable_printed_order_at_I :
    ¬ Summable (fun n : ℤ => ∑' k : ℕ, doubleTerm Complex.I n ((k : ℤ) + 1)) := by
  intro h
  have hRows (n : ℤ) :=
    tsum_at_I_eq_real (fun _ : ℕ => n) (fun k => (k : ℤ) + 1) (summable_real_row n)
  have hOuter : Summable (fun n : ℤ => ∑' k : ℕ, doubleTermRealAtI n ((k : ℤ) + 1)) := by
    simpa only [hRows, Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.summable h
  apply not_summable_joint_real
  exact (summable_prod_of_nonneg (f := fun p : ℤ × ℕ =>
    doubleTermRealAtI p.1 ((p.2 : ℤ) + 1)) (fun _ => Real.exp_nonneg _)).2
    ⟨summable_real_row, hOuter⟩

private theorem one_le_real_column_tsum (m : ℤ) (hm : 0 ≤ m) :
    1 ≤ ∑' n : ℤ, doubleTermRealAtI n m := by
  have hRidge : doubleTermRealAtI (-m - 1) m ≤ ∑' n : ℤ, doubleTermRealAtI n m :=
    (summable_real_column m).le_tsum (-m - 1) (fun _ _ => Real.exp_nonneg _)
  exact (one_le_doubleTermRealAtI_ridge m hm).trans hRidge

/-- Reversing the order also leaves a divergent outer sum at τ=i. -/
theorem not_summable_reversed_order_at_I :
    ¬ Summable (fun k : ℕ => ∑' n : ℤ, doubleTerm Complex.I n ((k : ℤ) + 1)) := by
  intro h
  have hColumns :
      (fun k : ℕ => ∑' n : ℤ, doubleTerm Complex.I n ((k : ℤ) + 1)) =
        (fun k : ℕ => Complex.ofReal (∑' n : ℤ, doubleTermRealAtI n ((k : ℤ) + 1))) := by
    funext k
    exact tsum_at_I_eq_real (fun n : ℤ => n) (fun _ : ℤ => (k : ℤ) + 1)
      (summable_real_column ((k : ℤ) + 1))
  rw [hColumns] at h
  have hOuter : Summable (fun k : ℕ => ∑' n : ℤ, doubleTermRealAtI n ((k : ℤ) + 1)) := by
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.summable h
  have hLower (k : ℕ) : 1 ≤ ∑' n : ℤ, doubleTermRealAtI n ((k : ℤ) + 1) :=
    one_le_real_column_tsum ((k : ℤ) + 1) (by omega)
  exact not_summable_of_one_le hLower hOuter

end ManuscriptAudit.AppellDoubleRidge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.AppellDoubleRidge.doubleExponent_ridge,
    ``ManuscriptAudit.AppellDoubleRidge.doubleTerm_at_I,
    ``ManuscriptAudit.AppellDoubleRidge.not_summable_joint_at_I,
    ``ManuscriptAudit.AppellDoubleRidge.not_summable_printed_order_at_I,
    ``ManuscriptAudit.AppellDoubleRidge.not_summable_reversed_order_at_I] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
