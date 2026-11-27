import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRatioCuspLimit

/-!
# Actual unitary eta phases at the two half-weights

The weight-positive phase is the true eta automorphy divided by its
absolute value. Multiplying by the inverse integral unit phase changes
the weight from positive one-half to negative one-half with the same
eta multiplier. All powers use the native modular denominator.
-/

namespace ManuscriptAudit.Paper8EtaHalfWeightPhase

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaRatioCuspLimit
open scoped MatrixGroups

noncomputable section

def positivePhase (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  ModularForm.eta (g • z : ℍ) /
    (ModularForm.eta z * (Real.sqrt ‖denominator g z‖ : ℂ))

def negativePhase (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  positivePhase g z * ((‖denominator g z‖ : ℂ) / denominator g z)

theorem positivePhase_norm (g : SL(2, ℤ)) (z : ℍ) :
    ‖positivePhase g z‖ = 1 := by
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have hEta : 0 < ‖ModularForm.eta z‖ := norm_pos_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  rw [positivePhase, norm_div, norm_mul, eta_norm_transform, Complex.norm_real, abs_of_pos hD,
    mul_comm (Real.sqrt ‖denominator g z‖)]
  exact div_self (mul_ne_zero hEta.ne' hD.ne')

theorem positivePhase_sq (g : SL(2, ℤ)) (z : ℍ) :
    positivePhase g z ^ 2 = squaredMultiplier g *
      (denominator g z / (‖denominator g z‖ : ℂ)) := by
  have hEta := ModularForm.eta_ne_zero z.im_pos
  have hN : (‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (denominator_ne_zero g z))
  have hSq : (Real.sqrt ‖denominator g z‖ : ℂ) ^ 2 = (‖denominator g z‖ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [positivePhase, div_pow, mul_pow, eta_squared_transform, hSq]
  field_simp [hEta, hN] <;> ring

theorem negativePhase_norm (g : SL(2, ℤ)) (z : ℍ) :
    ‖negativePhase g z‖ = 1 := by
  have hD : 0 < ‖denominator g z‖ := norm_pos_iff.mpr (denominator_ne_zero g z)
  rw [negativePhase, norm_mul, positivePhase_norm, norm_div, Complex.norm_real, abs_of_pos hD,
    div_self hD.ne', one_mul]

theorem negativePhase_sq (g : SL(2, ℤ)) (z : ℍ) :
    negativePhase g z ^ 2 = squaredMultiplier g *
      ((‖denominator g z‖ : ℂ) / denominator g z) := by
  have hD := denominator_ne_zero g z
  have hN : (‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hD)
  rw [negativePhase, mul_pow, positivePhase_sq, div_pow]
  field_simp [hD, hN] <;> ring

theorem conjugate_negativePhase_sq (g : SL(2, ℤ)) (z : ℍ) :
    ((starRingEnd ℂ) (negativePhase g z)) ^ 2 =
      (starRingEnd ℂ) (squaredMultiplier g) *
        (denominator g z / (‖denominator g z‖ : ℂ)) := by
  let d := denominator g z
  have hD : d ≠ 0 := denominator_ne_zero g z
  have hN : (‖d‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hD)
  have hConj : (starRingEnd ℂ) d ≠ 0 := by
    exact map_ne_zero (starRingEnd ℂ) hD
  have hRatio : (‖d‖ : ℂ) / (starRingEnd ℂ) d = d / (‖d‖ : ℂ) := by
    apply (div_eq_div_iff hConj hN).2
    rw [← pow_two]
    simpa only [Complex.ofReal_pow] using (Complex.mul_conj' d).symm
  rw [← map_pow, negativePhase_sq, map_mul, map_div₀, Complex.conj_ofReal, hRatio]

theorem inverse_quarterHeight_sq (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ).im ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) =
      ‖denominator g z‖ * (z.im ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) := by
  let d := ‖denominator g z‖
  have hd : 0 < d := norm_pos_iff.mpr (denominator_ne_zero g z)
  have hExp : (-(1 / 4 : ℝ)) * (2 : ℕ) = -(1 / 2 : ℝ) := by norm_num
  have hExp' : ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 := by norm_num
  rw [← Real.rpow_mul_natCast (g • z : ℍ).im_pos.le _ 2,
    ← Real.rpow_mul_natCast z.im_pos.le _ 2,
    hExp, ModularGroup.im_smul_eq_div_normSq, ← denominator_eq, Complex.normSq_eq_norm_sq,
    Real.div_rpow z.im_pos.le (sq_nonneg d), ← Real.rpow_natCast_mul hd.le, hExp',
    Real.rpow_neg_one]
  change z.im ^ (-(1 / 2 : ℝ)) / d⁻¹ = d * z.im ^ (-(1 / 2 : ℝ))
  rw [div_inv_eq_mul, mul_comm]

end
end ManuscriptAudit.Paper8EtaHalfWeightPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.positivePhase_norm,
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.positivePhase_sq,
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.negativePhase_norm,
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.negativePhase_sq,
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.conjugate_negativePhase_sq,
      ``ManuscriptAudit.Paper8EtaHalfWeightPhase.inverse_quarterHeight_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
