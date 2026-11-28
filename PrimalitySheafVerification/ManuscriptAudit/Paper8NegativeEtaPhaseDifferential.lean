import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Calculus
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassPhaseArgumentDerivative
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaHalfWeightPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassWirtinger

/-! Directional derivative of the actual negative-half eta multiplier on the upper half-plane. -/

namespace ManuscriptAudit.Paper8NegativeEtaPhaseDifferential

open Filter Set UpperHalfPlane ModularForm
open Paper8MaassPhaseArgumentDerivative Paper8EtaHalfWeightPhase
open Paper8MaassWirtinger Paper8ActualEtaSquaredModularity
open scoped MatrixGroups Topology

noncomputable section

def negativeEtaPhaseComplex (g : SL(2, ℤ)) (w : ℂ) : ℂ :=
  (ModularForm.eta (fractionalLinear g w) /
    (ModularForm.eta w * (Real.sqrt ‖denominator g w‖ : ℂ))) *
      ((‖denominator g w‖ : ℂ) / denominator g w)

theorem negativeEtaPhaseComplex_coe (g : SL(2, ℤ)) (z : ℍ) :
    negativeEtaPhaseComplex g z = negativePhase g z := by
  unfold negativeEtaPhaseComplex negativePhase positivePhase
  rw [fractionalLinear_eq]

theorem negativeEtaPhaseComplex_differentiableAt (g : SL(2, ℤ)) (z : ℍ) :
    DifferentiableAt ℝ (negativeEtaPhaseComplex g) (z : ℂ) := by
  have hIn : 0 < (fractionalLinear g z).im := by
    rw [fractionalLinear_eq, UpperHalfPlane.coe_im]
    exact (g • z).im_pos
  have hEta0 := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).restrictScalars ℝ
  have hEta1 := ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hIn).comp (z : ℂ)
    (fractionalLinear_hasDerivAt g z).differentiableAt).restrictScalars ℝ
  have hD : DifferentiableAt ℝ (denominator g) (z : ℂ) := by
    unfold denominator
    fun_prop
  have hDen := denominator_ne_zero g z
  have hn := norm_pos_iff.mpr hDen
  have hN := hD.norm hDen
  have hS : DifferentiableAt ℝ (fun w : ℂ => (Real.sqrt ‖denominator g w‖ : ℂ)) (z : ℂ) :=
    Complex.ofRealCLM.differentiableAt.comp _ (hN.sqrt hn.ne')
  have hNC : DifferentiableAt ℝ (fun w : ℂ => (‖denominator g w‖ : ℂ)) (z : ℂ) :=
    Complex.ofRealCLM.differentiableAt.comp _ hN
  have hEtaDen : ModularForm.eta z * (Real.sqrt ‖denominator g z‖ : ℂ) ≠ 0 :=
    mul_ne_zero (ModularForm.eta_ne_zero z.im_pos)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hn).ne')
  exact (hEta1.div (hEta0.mul hS) hEtaDen).mul (hNC.div hD hDen)

theorem negativeEtaPhaseComplex_fderiv (g : SL(2, ℤ)) (z : ℍ) (v : ℂ) :
    fderiv ℝ (negativeEtaPhaseComplex g) (z : ℂ) v =
      (-Complex.I / 2) * (((g 1 0 : ℂ) * v / denominator g z).im : ℂ) *
        negativePhase g z := by
  let w : ℂ := z
  let d : ℂ := denominator g w
  let e : ℂ := (g 1 0 : ℂ) * v
  let p : ℂ := negativePhase g z
  let p' : ℂ := fderiv ℝ (negativeEtaPhaseComplex g) w v
  let a : ℝ → ℂ := fun t => w + (t : ℂ) * v
  have ha₀ : a 0 = w := by simp [a]
  have ha : HasDerivAt a v 0 := by
    simpa only [a, Complex.ofReal_one, one_mul, zero_add] using
      (hasDerivAt_const (0 : ℝ) w).add (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const v)
  have hD (t : ℝ) : denominator g (a t) = d + (t : ℂ) * e := by
    unfold denominator a d e
    ring
  have hd : d ≠ 0 := denominator_ne_zero g z
  have hp : p ≠ 0 := by
    intro hp0
    have hN := negativePhase_norm g z
    change ‖p‖ = 1 at hN
    simp [hp0] at hN
  have hAt : HasFDerivAt (negativeEtaPhaseComplex g)
      (fderiv ℝ (negativeEtaPhaseComplex g) w) (a 0) := by
    rw [ha₀]
    exact (negativeEtaPhaseComplex_differentiableAt g z).hasFDerivAt
  have hP : HasDerivAt (fun t => negativeEtaPhaseComplex g (a t)) p' 0 :=
    hAt.comp_hasDerivAt 0 ha
  have hP2 : HasDerivAt (fun t => negativeEtaPhaseComplex g (a t) ^ 2) (2 * p * p') 0 := by
    have hTmp := hP.pow 2
    rw [ha₀, negativeEtaPhaseComplex_coe g z] at hTmp
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, p, mul_assoc] using hTmp
  have haIm₀ : 0 < (a 0).im := by rw [ha₀]; exact z.im_pos
  have hLocal : (fun t => negativeEtaPhaseComplex g (a t) ^ 2) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => squaredMultiplier g * (((‖d + (t : ℂ) * e‖ : ℝ) : ℂ) / (d + (t : ℂ) * e))) := by
    have hC : ContinuousAt (fun t => (a t).im) 0 :=
      Complex.continuous_im.continuousAt.comp ha.continuousAt
    filter_upwards [hC.tendsto.eventually (Ioi_mem_nhds haIm₀)] with t ht
    let u : ℍ := ⟨a t, ht⟩
    change negativeEtaPhaseComplex g (u : ℂ) ^ 2 =
      squaredMultiplier g * (((‖d + (t : ℂ) * e‖ : ℝ) : ℂ) / (d + (t : ℂ) * e))
    rw [negativeEtaPhaseComplex_coe g u, negativePhase_sq]
    change squaredMultiplier g * ((‖denominator g (a t)‖ : ℂ) / denominator g (a t)) = _
    rw [hD]
  have hQ := (hasDerivAt_inverse_argument_affine e hd).const_mul (squaredMultiplier g)
  have hP2' := hQ.congr_of_eventuallyEq hLocal
  have hEq := hP2.unique hP2'
  change 2 * p * p' =
      squaredMultiplier g * (-Complex.I * ((e / d).im : ℂ) * ((‖d‖ : ℂ) / d)) at hEq
  have hSq : p ^ 2 = squaredMultiplier g * ((‖d‖ : ℂ) / d) := negativePhase_sq g z
  change p' = (-Complex.I / 2) * ((e / d).im : ℂ) * p
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp)
  rw [hEq]
  linear_combination Complex.I * ((e / d).im : ℂ) * hSq

end
end ManuscriptAudit.Paper8NegativeEtaPhaseDifferential

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8NegativeEtaPhaseDifferential.negativeEtaPhaseComplex_fderiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
