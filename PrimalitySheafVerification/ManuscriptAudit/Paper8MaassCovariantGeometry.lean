import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassConnectionAlgebra
import PrimalitySheafVerification.ManuscriptAudit.Paper8NegativeEtaPhaseDifferential

/-! Exact geometric coefficients of the weight-negative-half covariant pullback. -/

namespace ManuscriptAudit.Paper8MaassCovariantGeometry

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8NegativeEtaPhaseDifferential Paper8MaassConnectionAlgebra
open Paper8EtaHalfWeightPhase
open scoped MatrixGroups

noncomputable section

def maassCovariantValue (F : ℂ → ℂ) (z : ℍ) (v : ℂ) : ℂ :=
  (z.im : ℂ) * fderiv ℝ F (z : ℂ) v + (Complex.I / 4) * (v.re : ℂ) * F z

def maassCovariantLinear (F : ℂ → ℂ) (z : ℍ) : ℂ →L[ℝ] ℂ :=
  (z.im : ℂ) • fderiv ℝ F (z : ℂ) +
    ((Complex.I / 4) * F z) • (Complex.ofRealCLM.comp Complex.reCLM)

theorem maassCovariantLinear_apply (F : ℂ → ℂ) (z : ℍ) (v : ℂ) :
    maassCovariantLinear F z v = maassCovariantValue F z v := by
  unfold maassCovariantLinear maassCovariantValue
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  change _ + ((Complex.I / 4) * F z) * (v.re : ℂ) = _
  ring

def oddMaassPullback (g : SL(2, ℤ)) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  (negativeEtaPhaseComplex g w)⁻¹ * F (fractionalLinear g w)

theorem oddMaassPullback_coe (g : SL(2, ℤ)) (F : ℂ → ℂ) (z : ℍ) :
    oddMaassPullback g F z = (negativePhase g z)⁻¹ * F (g • z : ℍ) := by
  unfold oddMaassPullback
  rw [negativeEtaPhaseComplex_coe, fractionalLinear_eq]

def moebiusFrameRotation (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  (starRingEnd ℂ) (denominator g z) / denominator g z

theorem norm_moebiusFrameRotation (g : SL(2, ℤ)) (z : ℍ) :
    ‖moebiusFrameRotation g z‖ = 1 := by
  unfold moebiusFrameRotation
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr (denominator_ne_zero g z))]

theorem shiftedFrameScaling (g : SL(2, ℤ)) (z : ℍ) (v : ℂ) :
    ((denominator g z) ^ 2)⁻¹ * v =
      ((Complex.normSq (denominator g z))⁻¹ : ℝ) • (moebiusFrameRotation g z * v) := by
  let d := denominator g z
  have hd : d ≠ 0 := denominator_ne_zero g z
  have hc : (starRingEnd ℂ) d ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hd
  change (d ^ 2)⁻¹ * v = (Complex.normSq d)⁻¹ • (((starRingEnd ℂ) d / d) * v)
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.normSq_eq_conj_mul_self]
  field_simp [hd, hc] <;> ring

theorem shiftedFrameDifferential (A : ℂ →L[ℝ] ℂ) (g : SL(2, ℤ)) (z : ℍ) (v : ℂ) :
    (z.im : ℂ) * A (((denominator g z) ^ 2)⁻¹ * v) =
      ((g • z).im : ℂ) * A (moebiusFrameRotation g z * v) := by
  rw [shiftedFrameScaling, map_smul, Complex.real_smul, ModularGroup.im_smul_eq_div_normSq,
    ← denominator_eq, Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem shiftedFrameRealPart (g : SL(2, ℤ)) (z : ℍ) (v : ℂ) :
    2 * z.im * (((g 1 0 : ℂ) * v / denominator g z).im) + v.re =
      (moebiusFrameRotation g z * v).re := by
  let d := denominator g z
  let c := (g 1 0 : ℝ)
  have hD : d.im = c * z.im := by
    unfold d c denominator
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
  have hC := hyperbolic_connection_correction_cancel (v := v) (denominator_ne_zero g z) z.im_ne_zero hD
  have hC' : (((g 1 0 : ℂ) * v / denominator g z).im) / 2 +
      v.re / (4 * z.im) - (moebiusFrameRotation g z * v).re / (4 * z.im) = 0 := by
    simpa only [c, d, Complex.ofReal_intCast, moebiusFrameRotation] using hC
  have hEq : (4 * z.im) * ((((g 1 0 : ℂ) * v / denominator g z).im) / 2 +
      v.re / (4 * z.im) - (moebiusFrameRotation g z * v).re / (4 * z.im)) =
      (2 * z.im * (((g 1 0 : ℂ) * v / denominator g z).im) + v.re) -
        (moebiusFrameRotation g z * v).re := by
    field_simp [z.im_ne_zero] <;> ring
  rw [hC', mul_zero] at hEq
  exact sub_eq_zero.mp hEq.symm

end
end ManuscriptAudit.Paper8MaassCovariantGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCovariantGeometry.shiftedFrameDifferential,
      ``ManuscriptAudit.Paper8MaassCovariantGeometry.shiftedFrameRealPart] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
