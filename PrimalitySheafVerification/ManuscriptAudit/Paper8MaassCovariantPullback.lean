import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCovariantGeometry

/-! Exact transformation of the negative-half covariant gradient under every modular chart. -/

namespace ManuscriptAudit.Paper8MaassCovariantPullback

open UpperHalfPlane
open Paper8MaassCovariantGeometry Paper8MaassConnectionAlgebra Paper8NegativeEtaPhaseDifferential
open Paper8ActualEtaSquaredModularity Paper8MaassWirtinger Paper8EtaHalfWeightPhase
open scoped MatrixGroups

noncomputable section

theorem oddMaassPullback_differentiableAt {F : ℂ → ℂ} (g : SL(2, ℤ)) (z : ℍ)
    (hF : DifferentiableAt ℝ F ((g • z : ℍ) : ℂ)) :
    DifferentiableAt ℝ (oddMaassPullback g F) (z : ℂ) := by
  have hFComp : DifferentiableAt ℝ (fun w : ℂ => F (fractionalLinear g w)) (z : ℂ) := by
    have hAt : DifferentiableAt ℝ F (fractionalLinear g z) := by rw [fractionalLinear_eq]; exact hF
    exact hAt.comp _ ((fractionalLinear_hasDerivAt g z).differentiableAt.restrictScalars ℝ)
  have hP : negativeEtaPhaseComplex g z ≠ 0 := by
    intro h
    rw [negativeEtaPhaseComplex_coe] at h
    have hn := negativePhase_norm g z
    simp [h] at hn
  have hPhaseInv : DifferentiableAt ℝ (fun w : ℂ => (negativeEtaPhaseComplex g w)⁻¹) (z : ℂ) :=
    ((differentiableAt_inv_iff.mpr hP).restrictScalars ℝ).comp _
      (negativeEtaPhaseComplex_differentiableAt g z)
  exact hPhaseInv.mul hFComp

theorem oddMaassPullback_fderiv {F : ℂ → ℂ} (g : SL(2, ℤ)) (z : ℍ)
    (hF : DifferentiableAt ℝ F ((g • z : ℍ) : ℂ)) (v : ℂ) :
    fderiv ℝ (oddMaassPullback g F) (z : ℂ) v =
      (negativePhase g z)⁻¹ *
        (fderiv ℝ F ((g • z : ℍ) : ℂ) (((denominator g z) ^ 2)⁻¹ * v) +
        (Complex.I / 2) * (((g 1 0 : ℂ) * v / denominator g z).im : ℂ) * F (g • z : ℍ)) := by
  let p := negativePhase g z
  let m : ℝ := ((g 1 0 : ℂ) * v / denominator g z).im
  let z' : ℂ := (g • z : ℍ)
  let u := ((denominator g z) ^ 2)⁻¹ * v
  let R := fderiv ℝ F z'
  let a (t : ℝ) : ℂ := (z : ℂ) + (t : ℂ) * v
  have ha₀ : a 0 = (z : ℂ) := by simp [a]
  have ha : HasDerivAt a v 0 := by
    simpa only [a, Complex.ofReal_one, one_mul, zero_add] using
      (hasDerivAt_const (0 : ℝ) (z : ℂ)).add (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const v)
  have hp : p ≠ 0 := by
    intro hp'
    have h := negativePhase_norm g z
    change ‖p‖ = 1 at h
    simp [hp'] at h
  have hG₀ : fractionalLinear g (a 0) = z' := by rw [ha₀, fractionalLinear_eq]
  have hFM : HasFDerivAt F R (fractionalLinear g (a 0)) := by rw [hG₀]; exact hF.hasFDerivAt
  have hG : HasDerivAt (fun t => fractionalLinear g (a t)) u 0 := by
    have h : HasFDerivAt (fractionalLinear g)
        (ContinuousLinearMap.toSpanSingleton ℂ ((denominator g z ^ 2)⁻¹) |>.restrictScalars ℝ) (a 0) := by
      rw [ha₀]
      exact (fractionalLinear_hasDerivAt g z).complexToReal_fderiv
    have hRay := h.comp_hasDerivAt 0 ha
    change HasDerivAt (fun t => fractionalLinear g (a t)) (v * ((denominator g z) ^ 2)⁻¹) 0 at hRay
    simpa only [u, mul_comm v] using hRay
  have hFR : HasDerivAt (fun t => F (fractionalLinear g (a t))) (R u) 0 :=
    hFM.comp_hasDerivAt 0 hG
  have hP : HasDerivAt (fun t => negativeEtaPhaseComplex g (a t)) ((-Complex.I / 2) * (m : ℂ) * p) 0 := by
    have hAt : HasFDerivAt (negativeEtaPhaseComplex g)
        (fderiv ℝ (negativeEtaPhaseComplex g) (z : ℂ)) (a 0) := by
      rw [ha₀]
      exact (negativeEtaPhaseComplex_differentiableAt g z).hasFDerivAt
    have h := hAt.comp_hasDerivAt 0 ha
    rw [negativeEtaPhaseComplex_fderiv g z v] at h
    exact h
  have hVal : negativeEtaPhaseComplex g (a 0) = p := by rw [ha₀, negativeEtaPhaseComplex_coe]
  have hProd := (hP.inv (by rw [hVal]; exact hp)).mul hFR
  have hPull := oddMaassPullback_differentiableAt g z hF
  have hAt : HasFDerivAt (oddMaassPullback g F) (fderiv ℝ (oddMaassPullback g F) (z : ℂ)) (a 0) := by
    rw [ha₀]
    exact hPull.hasFDerivAt
  have hRay := hAt.comp_hasDerivAt 0 ha
  have hEq := hRay.unique hProd
  change fderiv ℝ (oddMaassPullback g F) (z : ℂ) v =
    (-((-Complex.I / 2) * (m : ℂ) * p) / (negativeEtaPhaseComplex g (a 0)) ^ 2) * F (fractionalLinear g (a 0)) +
      (negativeEtaPhaseComplex g (a 0))⁻¹ * R u at hEq
  rw [hVal, hG₀] at hEq
  change fderiv ℝ (oddMaassPullback g F) (z : ℂ) v =
    p⁻¹ * (R u + (Complex.I / 2) * (m : ℂ) * F z')
  rw [hEq]
  field_simp [hp] <;> ring

theorem maassCovariantValue_pullback {F : ℂ → ℂ} (g : SL(2, ℤ)) (z : ℍ)
    (hF : DifferentiableAt ℝ F ((g • z : ℍ) : ℂ)) (v : ℂ) :
    maassCovariantValue (oddMaassPullback g F) z v =
      (negativePhase g z)⁻¹ * maassCovariantValue F (g • z)
        (moebiusFrameRotation g z * v) := by
  let m : ℝ := ((g 1 0 : ℂ) * v / denominator g z).im
  let p := negativePhase g z
  let A := fderiv ℝ F ((g • z : ℍ) : ℂ)
  unfold maassCovariantValue
  calc
    _ = p⁻¹ * ((z.im : ℂ) * A (((denominator g z) ^ 2)⁻¹ * v) +
        (Complex.I / 4) * ((2 * z.im * m + v.re : ℝ) : ℂ) * F (g • z : ℍ)) := by
      rw [oddMaassPullback_fderiv g z hF v, oddMaassPullback_coe]
      unfold m p A
      push_cast <;> ring
    _ = _ := by
      rw [shiftedFrameDifferential A g z v]
      have hRe : 2 * z.im * m + v.re = (moebiusFrameRotation g z * v).re :=
        shiftedFrameRealPart g z v
      rw [hRe]

def maassCovariantEnergy (F : ℂ → ℂ) (z : ℍ) : ℝ :=
  ‖maassCovariantValue F z 1‖ ^ 2 + ‖maassCovariantValue F z Complex.I‖ ^ 2

theorem maassCovariantEnergy_pullback {F : ℂ → ℂ} (g : SL(2, ℤ)) (z : ℍ)
    (hF : DifferentiableAt ℝ F ((g • z : ℍ) : ℂ)) :
    maassCovariantEnergy (oddMaassPullback g F) z = maassCovariantEnergy F (g • z) := by
  unfold maassCovariantEnergy
  rw [maassCovariantValue_pullback g z hF, maassCovariantValue_pullback g z hF]
  simp only [norm_mul, norm_inv, negativePhase_norm, inv_one, one_mul, mul_one]
  have h := realLinear_complex_unitRotation_energy
    (maassCovariantLinear F (g • z)) (norm_moebiusFrameRotation g z)
  simp only [maassCovariantLinear_apply] at h
  rwa [mul_comm Complex.I] at h

end
end ManuscriptAudit.Paper8MaassCovariantPullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassCovariantPullback.maassCovariantEnergy_pullback
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
