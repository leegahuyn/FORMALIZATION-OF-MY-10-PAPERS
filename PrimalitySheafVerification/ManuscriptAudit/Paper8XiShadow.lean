import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-!
# Conjugate-linear shadow scaling in Paper 8

Physical PDF pp. 303 and 336 define the conjugated Bruinier–Funke operator.
Physical p. 311, Proposition 2, multiplies the common shadow by the sum of
the block coefficients. For complex coefficients the multiplier is the
conjugate of that sum. The one-block comparison is conditional on the
specified shadow identity for a differentiable block and point.
-/

namespace ManuscriptAudit.Paper8XiShadow

open ManuscriptAudit.MaassLaplacian (partialX partialY)
open scoped BigOperators

noncomputable section

abbrev Field := ℝ → ℝ → ℂ

def scale (c : ℂ) (F : Field) : Field := fun x y => c * F x y

def dBar (F : Field) (x y : ℝ) : ℂ :=
  (partialX F x y + Complex.I * partialY F x y) / 2

def xiHalf (F : Field) (x y : ℝ) : ℂ :=
  2 * Complex.I * (Real.sqrt y : ℂ) * (starRingEnd ℂ) (dBar F x y)

private theorem partialX_scale (c : ℂ) (F : Field) (x y : ℝ) :
    partialX (scale c F) x y = c * partialX F x y :=
  deriv_const_mul_field c

private theorem partialY_scale (c : ℂ) (F : Field) (x y : ℝ) :
    partialY (scale c F) x y = c * partialY F x y :=
  deriv_const_mul_field c

private theorem dBar_scale (c : ℂ) (F : Field) (x y : ℝ) :
    dBar (scale c F) x y = c * dBar F x y := by
  unfold dBar
  rw [partialX_scale, partialY_scale]
  ring

/-- Conjugation of the coefficient is forced by the two coordinate derivatives. -/
theorem xiHalf_scale (c : ℂ) (F : Field) (x y : ℝ) :
    xiHalf (scale c F) x y = (starRingEnd ℂ) c * xiHalf F x y := by
  unfold xiHalf
  rw [dBar_scale, map_mul]
  ring

private theorem partialX_sum {J : Type*} (s : Finset J) (c : J → ℂ) (F : J → Field)
    {x y : ℝ} (hx : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j t y) x) :
    partialX (fun u v => ∑ j ∈ s, c j * F j u v) x y =
      ∑ j ∈ s, c j * partialX (F j) x y := by
  have h : ∀ j ∈ s, DifferentiableAt ℝ (fun t => c j * F j t y) x :=
    fun j hj => ((hx j hj).hasDerivAt.const_mul (c j)).differentiableAt
  unfold partialX
  rw [deriv_fun_sum h]
  simp only [deriv_const_mul_field]

private theorem partialY_sum {J : Type*} (s : Finset J) (c : J → ℂ) (F : J → Field)
    {x y : ℝ} (hy : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j x t) y) :
    partialY (fun u v => ∑ j ∈ s, c j * F j u v) x y =
      ∑ j ∈ s, c j * partialY (F j) x y := by
  have h : ∀ j ∈ s, DifferentiableAt ℝ (fun t => c j * F j x t) y :=
    fun j hj => ((hy j hj).hasDerivAt.const_mul (c j)).differentiableAt
  unfold partialY
  rw [deriv_fun_sum h]
  simp only [deriv_const_mul_field]

private theorem dBar_sum {J : Type*} (s : Finset J) (c : J → ℂ) (F : J → Field)
    {x y : ℝ} (hx : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j t y) x)
    (hy : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j x t) y) :
    dBar (fun u v => ∑ j ∈ s, c j * F j u v) x y =
      ∑ j ∈ s, c j * dBar (F j) x y := by
  unfold dBar
  rw [partialX_sum s c F hx, partialY_sum s c F hy,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem xiHalf_sum {J : Type*} (s : Finset J) (c : J → ℂ) (F : J → Field)
    {x y : ℝ} (hx : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j t y) x)
    (hy : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j x t) y) :
    xiHalf (fun u v => ∑ j ∈ s, c j * F j u v) x y =
      ∑ j ∈ s, (starRingEnd ℂ) (c j) * xiHalf (F j) x y := by
  simp only [xiHalf, dBar_sum s c F hx hy, map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- If the blocks share a shadow, the true multiplier is the conjugated coefficient sum. -/
theorem xiHalf_common_shadow {J : Type*} (s : Finset J) (c : J → ℂ) (F : J → Field)
    {x y : ℝ} {G : ℂ} (hx : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j t y) x)
    (hy : ∀ j ∈ s, DifferentiableAt ℝ (fun t => F j x t) y)
    (hG : ∀ j ∈ s, xiHalf (F j) x y = G) :
    xiHalf (fun u v => ∑ j ∈ s, c j * F j u v) x y =
      (starRingEnd ℂ) (∑ j ∈ s, c j) * G := by
  rw [xiHalf_sum s c F hx hy, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hG j hj]

theorem printed_multiplier_fails_at_nonzero_shadow {F : Field} {x y : ℝ} {G : ℂ}
    (hG : xiHalf F x y = G) (hne : G ≠ 0) :
    xiHalf (scale Complex.I F) x y ≠ Complex.I * G := by
  rw [xiHalf_scale, Complex.conj_I, hG]
  intro h
  have hz : (2 : ℂ) * (Complex.I * G) = 0 := by
    calc
      (2 : ℂ) * (Complex.I * G) = Complex.I * G + Complex.I * G := two_mul _
      _ = -Complex.I * G + Complex.I * G :=
        congrArg (fun z : ℂ => z + Complex.I * G) h.symm
      _ = 0 := by simp [neg_mul]
  exact (mul_ne_zero two_ne_zero (mul_ne_zero Complex.I_ne_zero hne)) hz

def printedTheta (τ : ℂ) : ℂ := jacobiTheta₂ ((-1 : ℂ) / 2) τ

theorem hasSum_printedTheta {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => Complex.exp
      ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ +
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((-1 : ℂ) / 2))) (printedTheta τ) := by
  simpa only [printedTheta, jacobiTheta₂_term, add_comm] using
    hasSum_jacobiTheta₂_term ((-1 : ℂ) / 2) hτ

private theorem thetaImaginary_term (n : ℤ) :
    jacobiTheta₂_term n (Complex.I / 2) Complex.I =
      (Real.exp (-Real.pi * ((n : ℝ) ^ 2 + (n : ℝ))) : ℂ) := by
  unfold jacobiTheta₂_term
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (Complex.I / 2) +
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Complex.I =
      (Real.pi : ℂ) * (n : ℂ) * Complex.I ^ 2 +
        (Real.pi : ℂ) * (n : ℂ) ^ 2 * Complex.I ^ 2 := by ring
    _ = -(Real.pi : ℂ) * ((n : ℂ) ^ 2 + (n : ℂ)) := by rw [Complex.I_sq]; ring

private theorem thetaImaginary_pos :
    0 < (jacobiTheta₂ (Complex.I / 2) Complex.I).re := by
  have h := hasSum_jacobiTheta₂_term (Complex.I / 2) (τ := Complex.I) (by simp)
  have hr : HasSum (fun n : ℤ => Real.exp (-Real.pi * ((n : ℝ) ^ 2 + (n : ℝ))))
      (jacobiTheta₂ (Complex.I / 2) Complex.I).re := by
    simpa only [Complex.reCLM_apply, thetaImaginary_term, Complex.ofReal_re] using
      Complex.reCLM.hasSum h
  have hle := hr.summable.sum_le_tsum ({0} : Finset ℤ) (fun (n : ℤ) _ =>
    (Real.exp_pos (-Real.pi * ((n : ℝ) ^ 2 + (n : ℝ)))).le)
  rw [hr.tsum_eq, Finset.sum_singleton] at hle
  exact (Real.exp_pos _).trans_le hle

/-- The exact bilateral theta printed in Proposition 2 is nonzero at `τ = i`.
The Jacobi transformation sends it to a series of positive real terms. -/
theorem printedTheta_at_I_ne_zero : printedTheta Complex.I ≠ 0 := by
  have hτ : (-1 : ℂ) / Complex.I = Complex.I := by
    apply (div_eq_iff Complex.I_ne_zero).2
    rw [← pow_two, Complex.I_sq]
  have hz : ((-1 : ℂ) / 2) / Complex.I = Complex.I / 2 := by
    apply (div_eq_iff Complex.I_ne_zero).2
    calc
      (-1 : ℂ) / 2 = Complex.I ^ 2 / 2 := by rw [Complex.I_sq]
      _ = Complex.I / 2 * Complex.I := by ring
  have hpow : -Complex.I * Complex.I = 1 := by rw [neg_mul, ← pow_two, Complex.I_sq, neg_neg]
  unfold printedTheta
  rw [jacobiTheta₂_functional_equation, hτ, hz, hpow, Complex.one_cpow, div_one, one_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h
  exact (ne_of_gt thetaImaginary_pos) (by rw [h, Complex.zero_re])

/-- The contradiction at the actual argument is conditional only on the one-block
shadow equation used in the printed proof, with its nonzero normalization. -/
theorem printed_theta_multiplier_fails_at_I {F : Field} {κ : ℂ} (hκ : κ ≠ 0)
    (hF : xiHalf F 0 1 = κ * printedTheta Complex.I) :
    xiHalf (scale Complex.I F) 0 1 ≠ Complex.I * (κ * printedTheta Complex.I) :=
  printed_multiplier_fails_at_nonzero_shadow hF (mul_ne_zero hκ printedTheta_at_I_ne_zero)

end

end ManuscriptAudit.Paper8XiShadow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8XiShadow.xiHalf_scale,
      ``ManuscriptAudit.Paper8XiShadow.xiHalf_common_shadow,
      ``ManuscriptAudit.Paper8XiShadow.printed_multiplier_fails_at_nonzero_shadow,
      ``ManuscriptAudit.Paper8XiShadow.hasSum_printedTheta,
      ``ManuscriptAudit.Paper8XiShadow.printedTheta_at_I_ne_zero,
      ``ManuscriptAudit.Paper8XiShadow.printed_theta_multiplier_fails_at_I] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
