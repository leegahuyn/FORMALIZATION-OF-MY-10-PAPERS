import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCovariantPullback
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCriticalOddVanishing

/-! Modular covariance of the sesquilinear flux associated with the actual odd Maass connection. -/

namespace ManuscriptAudit.Paper8OddMaassFluxTransport

open Filter Set UpperHalfPlane
open Paper8EtaCriticalOddVanishing Paper8OddCrossCuspRows Paper8EtaHalfWeightPhase
open Paper8MaassCovariantGeometry Paper8MaassCovariantPullback Paper8ActualEtaSquaredModularity
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq)
open scoped MatrixGroups Topology

noncomputable section

def oddMultiplierValue (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) : ℂ :=
  (levelCharacter g : ℂ) * negativePhase (g : SL(2, ℤ)) z

theorem norm_oddMultiplierValue (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    ‖oddMultiplierValue g z‖ = 1 := by
  have hSq : ‖(levelCharacter g : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, levelCharacter_sq, norm_one]
  have hC : ‖(levelCharacter g : ℂ)‖ = 1 := by nlinarith [norm_nonneg (levelCharacter g : ℂ)]
  unfold oddMultiplierValue
  rw [norm_mul, hC, negativePhase_norm, mul_one]

theorem conj_oddMultiplierValue_mul_self (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    (starRingEnd ℂ) (oddMultiplierValue g z) * oddMultiplierValue g z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, norm_oddMultiplierValue]
  norm_num

theorem maassCovariantValue_oddLaw_transport {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ z : ℍ, DifferentiableAt ℝ F z) (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) (v : ℂ) :
    maassCovariantValue F ((g : SL(2, ℤ)) • z) (moebiusFrameRotation (g : SL(2, ℤ)) z * v) =
      oddMultiplierValue g z * maassCovariantValue F z v := by
  let γ : SL(2, ℤ) := g
  let χ : ℂ := (levelCharacter g : ℂ)
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hp (u : ℍ) : negativePhase γ u ≠ 0 := by
    intro h
    have hN := negativePhase_norm γ u
    simp [h] at hN
  have hEq : oddMaassPullback γ F =ᶠ[𝓝 (z : ℂ)] (fun w => χ * F w) := by
    filter_upwards [hOpen.mem_nhds z.im_pos] with w hw
    let u : ℍ := ⟨w, hw⟩
    change oddMaassPullback γ F u = χ * F u
    rw [oddMaassPullback_coe, show F (γ • u : ℍ) = χ * negativePhase γ u * F u from hLaw g u]
    calc
      _ = ((negativePhase γ u)⁻¹ * negativePhase γ u) * (χ * F u) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (hp u), one_mul]
  have hValue : maassCovariantValue (oddMaassPullback γ F) z v = χ * maassCovariantValue F z v := by
    unfold maassCovariantValue
    rw [hEq.fderiv_eq (𝕜 := ℝ), hEq.self_of_nhds, fderiv_const_mul (hF z)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hCh := maassCovariantValue_pullback γ z (hF (γ • z)) v
  rw [hValue] at hCh
  change maassCovariantValue F (γ • z) (moebiusFrameRotation γ z * v) =
    (χ * negativePhase γ z) * maassCovariantValue F z v
  calc
    _ = negativePhase γ z * ((negativePhase γ z)⁻¹ *
        maassCovariantValue F (γ • z) (moebiusFrameRotation γ z * v)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (hp z), one_mul]
    _ = _ := by rw [← hCh]; ring

def sesquilinearCovariantFlux (F G : ℂ → ℂ) (z : ℍ) : ℂ →L[ℝ] ℂ :=
  ((starRingEnd ℂ) (G z) / (z.im : ℂ)) • maassCovariantLinear F z

theorem sesquilinearCovariantFlux_apply (F G : ℂ → ℂ) (z : ℍ) (v : ℂ) :
    sesquilinearCovariantFlux F G z v =
      ((starRingEnd ℂ) (G z) / (z.im : ℂ)) * maassCovariantValue F z v := by
  unfold sesquilinearCovariantFlux
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, maassCovariantLinear_apply]

theorem sesquilinearCovariantFlux_transport {F G : ℂ → ℂ} (hF : OddMaassLaw F) (hG : OddMaassLaw G)
    (hD : ∀ z : ℍ, DifferentiableAt ℝ F z) (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) (v : ℂ) :
    sesquilinearCovariantFlux F G ((g : SL(2, ℤ)) • z)
        (moebiusFrameRotation (g : SL(2, ℤ)) z * v) =
      (Complex.normSq (denominator (g : SL(2, ℤ)) z) : ℂ) * sesquilinearCovariantFlux F G z v := by
  let γ : SL(2, ℤ) := g
  let p := oddMultiplierValue g z
  let d := denominator γ z
  have hU : G (γ • z : ℍ) = p * G z := hG g z
  have hP : (starRingEnd ℂ) p * p = 1 := conj_oddMultiplierValue_mul_self g z
  have hD₀ : (Complex.normSq d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr (denominator_ne_zero γ z)).ne'
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  rw [sesquilinearCovariantFlux_apply, sesquilinearCovariantFlux_apply, maassCovariantValue_oddLaw_transport hF hD,
    hU, map_mul]
  change ((starRingEnd ℂ) p * (starRingEnd ℂ) (G z) / ((γ • z).im : ℂ)) *
      (p * maassCovariantValue F z v) = _
  calc
    _ = ((starRingEnd ℂ) p * p) *
        (((starRingEnd ℂ) (G z) / ((γ • z).im : ℂ)) * maassCovariantValue F z v) := by ring
    _ = _ := by
      rw [hP, one_mul, ModularGroup.im_smul_eq_div_normSq, ← denominator_eq, Complex.ofReal_div]
      change _ = (Complex.normSq d : ℂ) * (((starRingEnd ℂ) (G z) / (z.im : ℂ)) * maassCovariantValue F z v)
      field_simp [hy, hD₀] <;> ring

def realProjectedFluxForm (P : ℂ →L[ℝ] ℝ) (F G : ℂ → ℂ) (z : ℍ) : ℂ :=
  (P (sesquilinearCovariantFlux F G z Complex.I) : ℂ) +
    Complex.I * (P (sesquilinearCovariantFlux F G z 1) : ℂ)

private theorem real_linear_frame_components (A : ℂ →L[ℝ] ℝ) (v : ℂ) :
    A v = v.re * A 1 + v.im * A Complex.I := by
  have h : v.re • (1 : ℂ) + v.im • Complex.I = v := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im v
  calc
    _ = A (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg A h.symm
    _ = _ := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem realProjectedFluxForm_weight_two (P : ℂ →L[ℝ] ℝ) {F G : ℂ → ℂ}
    (hF : OddMaassLaw F) (hG : OddMaassLaw G) (hD : ∀ z : ℍ, DifferentiableAt ℝ F z)
    (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    realProjectedFluxForm P F G ((g : SL(2, ℤ)) • z) =
      (denominator (g : SL(2, ℤ)) z) ^ 2 * realProjectedFluxForm P F G z := by
  let γ : SL(2, ℤ) := g
  let w : ℍ := γ • z
  let d := denominator γ z
  let r := moebiusFrameRotation γ z
  let C := Complex.normSq d
  let A := P.comp (sesquilinearCovariantFlux F G z)
  let B := P.comp (sesquilinearCovariantFlux F G w)
  have hUp (v : ℂ) : B (r * v) = C * A v := by
    have h := congrArg P (sesquilinearCovariantFlux_transport hF hG hD g z v)
    change B (r * v) = P ((C : ℂ) * sesquilinearCovariantFlux F G z v) at h
    rw [← Complex.real_smul, map_smul] at h
    exact h
  have ha := hUp 1
  rw [mul_one, real_linear_frame_components B r] at ha
  have hb := hUp Complex.I
  rw [real_linear_frame_components B (r * Complex.I)] at hb
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero] at hb
  have hEq : r * ((B Complex.I : ℂ) + Complex.I * (B 1 : ℂ)) =
      (C : ℂ) * ((A Complex.I : ℂ) + Complex.I * (A 1 : ℂ)) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, one_mul, mul_one, sub_zero, add_zero, zero_add]
    · linarith only [hb]
    · linarith only [ha]
  have hProd : r * d ^ 2 = (C : ℂ) := by
    unfold r d C moebiusFrameRotation
    rw [Complex.normSq_eq_conj_mul_self]
    field_simp [denominator_ne_zero γ z] <;> ring
  have hr : r ≠ 0 := by
    intro h
    have hN := norm_moebiusFrameRotation γ z
    change ‖r‖ = 1 at hN
    simp [h] at hN
  change ((B Complex.I : ℂ) + Complex.I * (B 1 : ℂ)) =
    d ^ 2 * ((A Complex.I : ℂ) + Complex.I * (A 1 : ℂ))
  apply mul_left_cancel₀ hr
  rw [hEq, ← mul_assoc, hProd]

end
end ManuscriptAudit.Paper8OddMaassFluxTransport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassFluxTransport.realProjectedFluxForm_weight_two
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
