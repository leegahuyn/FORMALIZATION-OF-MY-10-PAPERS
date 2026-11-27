import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowNonzero

/-!
# The unweighted half-integer shadow printed on physical p. 335

The index is the full coset ¹⁄₂ + ℤ and the printed coefficient is exactly
ν. Opposite half-integers contribute opposite terms. Absolute convergence
on the upper half-plane follows from Mathlib's Jacobi theta and its
elliptic derivative. The p. 338 nonzero Kronecker target is separate.
-/

namespace ManuscriptAudit.Paper8HalfIntegerShadow

noncomputable section

def halfIndex (n : ℤ) : ℂ := (n : ℂ) + 1 / 2

def term (τ : ℂ) (n : ℤ) : ℂ :=
  halfIndex n * Complex.exp ((Real.pi : ℂ) * Complex.I * (halfIndex n) ^ 2 * τ)

def printedShadow (τ : ℂ) : ℂ := ∑' n : ℤ, term τ n

theorem term_reflection (τ : ℂ) (n : ℤ) :
    term τ (-(n + 1)) = -term τ n := by
  have h : halfIndex (-(n + 1)) = -halfIndex n := by
    simp only [halfIndex, Int.cast_neg, Int.cast_add, Int.cast_one]
    ring
  simp only [term, h, neg_sq, neg_mul]

private theorem term_eq_theta (τ : ℂ) (n : ℤ) :
    term τ n =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) *
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * jacobiTheta₂'_term n (τ / 2) τ +
          (1 / 2 : ℂ) * jacobiTheta₂_term n (τ / 2) τ) := by
  have hCoef : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [jacobiTheta₂'_term, ← mul_assoc
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)),
    ← mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) (2 * (Real.pi : ℂ) * Complex.I),
    inv_mul_cancel₀ hCoef, one_mul, ← add_mul]
  rw [term, halfIndex, ← mul_left_comm ((n : ℂ) + 1 / 2),
    jacobiTheta₂_term, ← Complex.exp_add]
  apply congrArg (fun w : ℂ => ((n : ℂ) + 1 / 2) * Complex.exp w)
  ring

theorem absolute_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n => ‖term τ n‖) := by
  apply (summable_norm_iff (E := ℂ)).2
  have hTheta := (summable_jacobiTheta₂_term_iff (τ / 2) τ).2 hτ
  have hDeriv := (summable_jacobiTheta₂'_term_iff (τ / 2) τ).2 hτ
  have hSum := ((hDeriv.mul_left ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)).add
    (hTheta.mul_left (1 / 2 : ℂ))).mul_left (Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4))
  exact hSum.congr (fun n => (term_eq_theta τ n).symm)

theorem hasSum_zero {τ : ℂ} (hτ : 0 < τ.im) : HasSum (term τ) 0 := by
  have hSum := (absolute_summable hτ).of_norm
  have hPaired := hSum.hasSum.nat_add_neg_add_one
  have hPair : (fun n : ℕ => term τ (n : ℤ) + term τ (-((n : ℤ) + 1))) =
      (0 : ℕ → ℂ) := by
    funext n
    simp only [term_reflection, add_neg_cancel, Pi.zero_apply]
  rw [hPair] at hPaired
  exact (hPaired.unique _root_.hasSum_zero) ▸ hSum.hasSum

theorem printedShadow_eq_zero {τ : ℂ} (hτ : 0 < τ.im) : printedShadow τ = 0 :=
  (hasSum_zero hτ).tsum_eq

theorem incompatible_nonzero_kronecker_shadow (c d : ℂ) (hd : d ≠ 0) :
    ¬ (∀ τ : ℂ, 0 < τ.im →
      c * printedShadow τ = d * Paper8KroneckerShadow.unaryShadow τ) := by
  intro h
  obtain ⟨τ, hτ, hNonzero⟩ := Paper8KroneckerShadowNonzero.unaryShadow_nonzero_on_upper_half_plane
  have hEq := h τ hτ
  rw [printedShadow_eq_zero hτ, mul_zero] at hEq
  exact (mul_ne_zero hd hNonzero) hEq.symm

end
end ManuscriptAudit.Paper8HalfIntegerShadow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8HalfIntegerShadow.term_reflection,
      ``ManuscriptAudit.Paper8HalfIntegerShadow.absolute_summable,
      ``ManuscriptAudit.Paper8HalfIntegerShadow.hasSum_zero,
      ``ManuscriptAudit.Paper8HalfIntegerShadow.printedShadow_eq_zero,
      ``ManuscriptAudit.Paper8HalfIntegerShadow.incompatible_nonzero_kronecker_shadow] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
