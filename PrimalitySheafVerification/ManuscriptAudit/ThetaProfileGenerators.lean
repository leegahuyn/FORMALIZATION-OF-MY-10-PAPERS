import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9ThetaCuspLTwo

/-! The three genuine theta profiles under the modular generators. -/

namespace ManuscriptAudit.ThetaProfileGenerators

open Paper9ThetaCuspPhases Paper9ThetaCuspLTwo
open ModularGroup (S T)
open scoped UpperHalfPlane

noncomputable section

def thetaAlternating (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ

theorem thetaHalfShift_add_one (τ : ℂ) :
    thetaHalfShift (τ + 1) =
      Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * thetaHalfShift τ := by
  rw [thetaHalfShift_eq_tsum, thetaHalfShift_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  obtain ⟨k, hk⟩ := int_square_eq_add_twice n
  have hc : (n : ℂ) ^ 2 = (n : ℂ) + 2 * (k : ℂ) := by exact_mod_cast hk
  have hExp : (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * (τ + 1) =
      (Real.pi : ℂ) * Complex.I / 4 +
        (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * τ +
        ((n + k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination ((Real.pi : ℂ) * Complex.I) * hc
  rw [halfTerm, halfTerm, hExp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, Complex.exp_add]

/-- The squared norm density after the quarter-power height weighting. -/
def thetaDensity (F : ℂ → ℂ) (z : ℍ) : ℝ :=
  Real.sqrt z.im * ‖F (z : ℂ)‖ ^ (2 : ℕ)

private theorem coe_T_smul (z : ℍ) : ((T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  simp [add_comm]

private theorem im_T_smul (z : ℍ) : (T • z).im = z.im := by
  change (((T • z : ℍ) : ℂ)).im = z.im
  rw [coe_T_smul]
  simp

theorem thetaDensity_T_standard (z : ℍ) :
    thetaDensity jacobiTheta (T • z) = thetaDensity thetaAlternating z := by
  simp only [thetaDensity, coe_T_smul, im_T_smul, jacobiTheta_add_one_profile, thetaAlternating]

theorem thetaDensity_T_alternating (z : ℍ) :
    thetaDensity thetaAlternating (T • z) = thetaDensity jacobiTheta z := by
  unfold thetaDensity thetaAlternating
  rw [coe_T_smul, im_T_smul, ← jacobiTheta_add_one_profile,
    add_assoc, show (1 + 1 : ℂ) = 2 by norm_num, add_comm (z : ℂ) 2, jacobiTheta_two_add]
  
theorem thetaDensity_T_half (z : ℍ) :
    thetaDensity thetaHalfShift (T • z) = thetaDensity thetaHalfShift z := by
  have h : ‖Complex.exp ((Real.pi : ℂ) * Complex.I / 4)‖ = 1 := by
    rw [show (Real.pi : ℂ) * Complex.I / 4 = Complex.ofReal (Real.pi / 4) * Complex.I by
      push_cast
      ring, Complex.norm_exp, Complex.mul_I_re]
    simp
  rw [thetaDensity, thetaDensity, coe_T_smul, im_T_smul, thetaHalfShift_add_one, norm_mul, h,
    one_mul]

private theorem thetaWeightFactor_norm_sq (z : ℍ) :
    ‖thetaWeightFactor z‖ ^ (2 : ℕ) = ‖(z : ℂ)‖ := by
  have h : thetaWeightFactor z ^ (2 : ℕ) = -Complex.I * (z : ℂ) := by
    simpa only [thetaWeightFactor, one_div] using
      Complex.cpow_ofNat_inv_pow (-Complex.I * (z : ℂ)) 2
  rw [← norm_pow, h, norm_mul, norm_neg, Complex.norm_I, one_mul]

private theorem thetaDensity_S_of_transform (F G : ℂ → ℂ) (z : ℍ)
    (h : F ((S • z : ℍ) : ℂ) = thetaWeightFactor z * G (z : ℂ)) :
    thetaDensity F (S • z) = thetaDensity G z := by
  have hn : ‖(z : ℂ)‖ ≠ 0 := by
    intro he
    have hz := norm_eq_zero.mp he
    exact z.im_pos.ne' (by simpa using congrArg Complex.im hz)
  unfold thetaDensity
  rw [h, norm_mul, mul_pow, thetaWeightFactor_norm_sq, ModularGroup.im_smul_eq_div_normSq,
    ModularGroup.denom_S, ← Complex.sq_norm, Real.sqrt_div z.im_pos.le,
    Real.sqrt_sq (norm_nonneg _), ← mul_assoc, div_mul_cancel₀ _ hn]

theorem thetaDensity_S_standard (z : ℍ) :
    thetaDensity jacobiTheta (S • z) = thetaDensity jacobiTheta z :=
  thetaDensity_S_of_transform jacobiTheta jacobiTheta z (jacobiTheta_S_smul z)

theorem thetaDensity_S_alternating (z : ℍ) :
    thetaDensity thetaAlternating (S • z) = thetaDensity thetaHalfShift z := by
  apply thetaDensity_S_of_transform
  simpa [thetaAlternating, UpperHalfPlane.modular_S_smul, neg_div, one_div] using
    thetaHalfShift_inversion z

theorem thetaDensity_S_half (z : ℍ) :
    thetaDensity thetaHalfShift (S • z) = thetaDensity thetaAlternating z := by
  have h := thetaDensity_S_alternating (S • z)
  have hS : S • (S • z) = z := by
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.modular_S_smul, inv_neg]
  rw [hS] at h
  exact h.symm

end
end ManuscriptAudit.ThetaProfileGenerators

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaProfileGenerators.thetaHalfShift_add_one,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_T_standard,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_T_alternating,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_T_half,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_S_standard,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_S_alternating,
      ``ManuscriptAudit.ThetaProfileGenerators.thetaDensity_S_half] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
