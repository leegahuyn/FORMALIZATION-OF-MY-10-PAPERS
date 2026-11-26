import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CompactModularCore

/-!
# The unbarred product of the two positive half-weight factors

Paper 9, physical page 420, Section 3.1. Multiplication of two
positive half-weight factors with the standard Jacobi-theta laws leaves
a nonreal factor along a level-two parabolic action. A positive real
height power cannot remove this factor at a point where the product
is nonzero. The standard Jacobi theta supplies genuine test factors.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace ManuscriptAudit.Paper9UnbarredWeight

open LiteralCuspTruncation (GammaTwo OrbitQuotient orbitPoint)
open CompactModularCore (reduceTwo mem_gamma_iff_reduced_one)
open ModularGroup (S T)

noncomputable section

private def parabolic : SL(2, ℤ) := S * T ^ (2 : ℕ) * S

private theorem parabolic_mem : parabolic ∈ GammaTwo := by
  apply (mem_gamma_iff_reduced_one _).mpr
  have hT : reduceTwo (T ^ (2 : ℕ)) = 1 := by decide
  have hS : reduceTwo (S * S) = 1 := by decide
  rw [parabolic, map_mul, map_mul, hT, mul_one, ← map_mul, hS]

private theorem coe_ne_zero (z : ℍ) : (z : ℂ) ≠ 0 := by
  intro h
  exact z.im_pos.ne' (by simpa using congrArg Complex.im h)

private theorem coe_T_sq_S_smul (z : ℍ) :
    ((T ^ (2 : ℕ) • (S • z) : ℍ) : ℂ) = 2 - 1 / (z : ℂ) := by
  have h : T ^ (2 : ℕ) = T ^ (2 : ℤ) := rfl
  rw [h, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    UpperHalfPlane.modular_S_smul]
  simp [one_div, sub_eq_add_neg]

private def weightFactor (z : ℍ) : ℂ := (-Complex.I * (z : ℂ)) ^ (1 / 2 : ℂ)

private theorem weightFactor_sq (z : ℍ) : weightFactor z ^ 2 = -Complex.I * (z : ℂ) := by
  simpa only [weightFactor, one_div] using
    Complex.cpow_ofNat_inv_pow (-Complex.I * (z : ℂ)) 2

def StandardPositiveThetaCovariance (F : ℍ → ℂ) : Prop :=
  (∀ z : ℍ, F (S • z) = weightFactor z * F z) ∧
    (∀ z : ℍ, F (T ^ (2 : ℕ) • z) = F z)

private theorem product_parabolic (F G : ℍ → ℂ)
    (hF : StandardPositiveThetaCovariance F) (hG : StandardPositiveThetaCovariance G) (z : ℍ) :
    F (parabolic • z) * G (parabolic • z) =
      (1 - 2 * (z : ℂ)) * (F z * G z) := by
  have hS (w : ℍ) : F (S • w) * G (S • w) =
      (-Complex.I * (w : ℂ)) * (F w * G w) := by
    rw [hF.1, hG.1, ← weightFactor_sq]
    ring
  rw [parabolic, mul_smul, mul_smul, hS, hF.2, hG.2, hS, coe_T_sq_S_smul]
  have hFactor : (-Complex.I * (2 - 1 / (z : ℂ))) * (-Complex.I * (z : ℂ)) =
      1 - 2 * (z : ℂ) := by
    calc
      _ = (Complex.I * Complex.I) * ((2 - 1 / (z : ℂ)) * (z : ℂ)) := by ring
      _ = _ := by
        rw [Complex.I_mul_I, sub_mul, div_mul_cancel₀ _ (coe_ne_zero z)]
        ring
  rw [← mul_assoc, hFactor]

def heightWeightedProduct (a : ℝ) (F G : ℍ → ℂ) (z : ℍ) : ℂ :=
  ((z.im ^ a : ℝ) : ℂ) * (F z * G z)

theorem no_invariant_unbarred_product (a : ℝ) (F G : ℍ → ℂ)
    (hF : StandardPositiveThetaCovariance F) (hG : StandardPositiveThetaCovariance G)
    (z : ℍ) (hz : F z * G z ≠ 0) :
    ¬ ∃ K : OrbitQuotient → ℂ,
      ∀ w : ℍ, K (orbitPoint w) = heightWeightedProduct a F G w := by
  rintro ⟨K, hK⟩
  let g : GammaTwo := ⟨parabolic, parabolic_mem⟩
  let w := g • z
  have hOrbit : orbitPoint w = orbitPoint z := Quotient.sound ⟨g, rfl⟩
  have hEq : heightWeightedProduct a F G w = heightWeightedProduct a F G z :=
    (hK w).symm.trans ((congrArg K hOrbit).trans (hK z))
  have hProd : F w * G w = (1 - 2 * (z : ℂ)) * (F z * G z) :=
    product_parabolic F G hF hG z
  rw [heightWeightedProduct, heightWeightedProduct, hProd, ← mul_assoc] at hEq
  have hMul := mul_right_cancel₀ hz hEq
  have hIm : w.im ^ a * (-(2 * z.im)) = 0 := by
    simpa [Complex.mul_im, Complex.sub_im] using congrArg Complex.im hMul
  exact (mul_ne_zero (Real.rpow_pos_of_pos w.im_pos a).ne'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) z.im_pos.ne'))) hIm

private theorem jacobiTheta_I_ne_zero : jacobiTheta Complex.I ≠ 0 := by
  have hSum := hasSum_jacobiTheta₂_term 0 (τ := Complex.I) (by simp)
  have hTerm (n : ℤ) : (jacobiTheta₂_term n 0 Complex.I).re =
      Real.exp (-Real.pi * (n : ℝ) ^ 2) := by
    rw [jacobiTheta₂_term, mul_zero, zero_add]
    have h : (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * Complex.I =
        ((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      calc
        _ = (Real.pi : ℂ) * (n : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [h, ← Complex.ofReal_exp, Complex.ofReal_re]
  have hReal : HasSum (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2))
      (jacobiTheta Complex.I).re := by
    rw [jacobiTheta_eq_jacobiTheta₂]
    simpa only [Complex.reCLM_apply, hTerm] using Complex.reCLM.hasSum hSum
  have he := hReal.summable.sum_le_tsum ({0} : Finset ℤ)
    (fun n _ => (Real.exp_pos (-Real.pi * (n : ℝ) ^ 2)).le)
  rw [hReal.tsum_eq, Finset.sum_singleton] at he
  have hp : 0 < (jacobiTheta Complex.I).re := (Real.exp_pos _).trans_le he
  intro h
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl _) hp

theorem jacobi_theta_unbarred_product_does_not_descend (a : ℝ) :
    ¬ ∃ K : OrbitQuotient → ℂ, ∀ w : ℍ,
      K (orbitPoint w) =
        heightWeightedProduct a (fun z => jacobiTheta z) (fun z => jacobiTheta z) w := by
  have hc : StandardPositiveThetaCovariance (fun z => jacobiTheta z) :=
    ⟨jacobiTheta_S_smul, jacobiTheta_T_sq_smul⟩
  exact no_invariant_unbarred_product a _ _ hc hc ⟨Complex.I, by simp⟩
    (mul_ne_zero jacobiTheta_I_ne_zero jacobiTheta_I_ne_zero)

end

end ManuscriptAudit.Paper9UnbarredWeight

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9UnbarredWeight.no_invariant_unbarred_product,
      ``ManuscriptAudit.Paper9UnbarredWeight.jacobi_theta_unbarred_product_does_not_descend] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
