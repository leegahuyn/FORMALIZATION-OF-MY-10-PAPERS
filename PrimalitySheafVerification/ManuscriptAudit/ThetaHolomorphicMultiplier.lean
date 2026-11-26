import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Convex.Basic
import PrimalitySheafVerification.ManuscriptAudit.ThetaGlobalSection

/-!
# The holomorphic theta multiplier on the actual level-two group

The ratio by the principal square root is holomorphic and has constant
norm one. The maximum modulus principle identifies it with a single
phase for each group element.
-/

namespace ManuscriptAudit.ThetaHolomorphicMultiplier

open Set Matrix
open LiteralCuspTruncation (GammaTwo)
open ThetaGlobalSection ThetaProfileGenerators ThetaGammaTwoMetric
open scoped MatrixGroups UpperHalfPlane

noncomputable section

private def mobius (g : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  UpperHalfPlane.num (g : GL (Fin 2) ℝ) τ / UpperHalfPlane.denom (g : GL (Fin 2) ℝ) τ

private theorem mobius_coe (g : SL(2, ℤ)) (z : ℍ) : mobius g (z : ℂ) = (g • z : ℍ) := by
  change UpperHalfPlane.num (g : GL (Fin 2) ℝ) z /
    UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z = ((g : GL (Fin 2) ℝ) • z : ℍ)
  exact (UpperHalfPlane.coe_smul_of_det_pos (by simp) z).symm

def halfFactor (g : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  Complex.sqrt (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) τ)

private theorem halfFactor_sq (g : SL(2, ℤ)) (z : ℍ) :
    halfFactor g z ^ (2 : ℕ) = UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z := by
  rw [halfFactor, Complex.sqrt, pow_two,
    ← Complex.cpow_add _ _ (UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z),
    show (2 : ℂ)⁻¹ + 2⁻¹ = 1 by norm_num, Complex.cpow_one]

private theorem halfFactor_ne_zero (g : SL(2, ℤ)) (z : ℍ) : halfFactor g z ≠ 0 := by
  intro hz
  have h := halfFactor_sq g z
  rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  exact UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) z h.symm

private theorem denom_differentiable (g : GL (Fin 2) ℝ) (τ : ℂ) :
    DifferentiableAt ℂ (UpperHalfPlane.denom g) τ := by
  unfold UpperHalfPlane.denom
  fun_prop

private theorem halfFactor_differentiable (g : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (halfFactor g) τ := by
  let G : GL (Fin 2) ℝ := g
  by_cases hc : G 1 0 = 0
  · have he : halfFactor g = fun _ => Complex.sqrt (G 1 1 : ℂ) := by
      funext z
      change Complex.sqrt (UpperHalfPlane.denom G z) = Complex.sqrt (G 1 1 : ℂ)
      simp [UpperHalfPlane.denom, hc]
    rw [he]
    exact differentiableAt_const _
  · have he : (UpperHalfPlane.denom G τ).im = G 1 0 * τ.im := by
      simp [UpperHalfPlane.denom, Complex.mul_im]
    have hNonzero : (UpperHalfPlane.denom G τ).im ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc hτ.ne'
    have hSlit := Complex.mem_slitPlane_iff.mpr (Or.inr hNonzero)
    exact (Complex.differentiableAt_sqrt hSlit).comp τ (denom_differentiable G τ)

def ratio (γ : GammaTwo) (τ : ℂ) : ℂ :=
  jacobiTheta (mobius (γ : SL(2, ℤ)) τ) /
    (halfFactor (γ : SL(2, ℤ)) τ * jacobiTheta τ)

private theorem ratio_differentiable (γ : GammaTwo) :
    DifferentiableOn ℂ (ratio γ) UpperHalfPlane.upperHalfPlaneSet := by
  intro τ hτ
  let z : ℍ := ⟨τ, hτ⟩
  let g : SL(2, ℤ) := γ
  let G : GL (Fin 2) ℝ := g
  have hG : DifferentiableAt ℂ (mobius g) τ := by
    have hn : DifferentiableAt ℂ (UpperHalfPlane.num G) τ := by
      unfold UpperHalfPlane.num
      fun_prop
    exact hn.div (denom_differentiable G τ) (UpperHalfPlane.denom_ne_zero G z)
  have hIm : 0 < (mobius g τ).im := by
    change 0 < (mobius g (z : ℂ)).im
    rw [mobius_coe]
    exact (g • z).im_pos
  exact ((differentiableAt_jacobiTheta hIm).comp τ hG).div
    ((halfFactor_differentiable g hτ).mul (differentiableAt_jacobiTheta hτ))
    (mul_ne_zero (halfFactor_ne_zero g z) (jacobiTheta_ne_zero_upperHalfPlane z))
    |>.differentiableWithinAt

private theorem theta_norm_sq_smul (γ : GammaTwo) (z : ℍ) :
    ‖jacobiTheta ((γ • z : ℍ) : ℂ)‖ ^ (2 : ℕ) =
      ‖UpperHalfPlane.denom (↑(γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z‖ *
        ‖jacobiTheta (z : ℂ)‖ ^ (2 : ℕ) := by
  let g : SL(2, ℤ) := γ
  let G : GL (Fin 2) ℝ := g
  have hPos : 0 < ‖UpperHalfPlane.denom G z‖ :=
    norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero G z)
  have hHeight : Real.sqrt (g • z).im =
      Real.sqrt z.im / ‖UpperHalfPlane.denom G z‖ := by
    rw [ModularGroup.im_smul_eq_div_normSq, Real.sqrt_div z.im_pos.le,
      Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hD := thetaDensity_invariant g γ.property z
  change Real.sqrt (g • z).im * ‖jacobiTheta ((g • z : ℍ) : ℂ)‖ ^ (2 : ℕ) =
    Real.sqrt z.im * ‖jacobiTheta (z : ℂ)‖ ^ (2 : ℕ) at hD
  rw [hHeight, div_mul_eq_mul_div] at hD
  have h := (div_eq_iff hPos.ne').mp hD
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr z.im_pos).ne'
  exact h.trans (by ring)

theorem ratio_norm (γ : GammaTwo) (z : ℍ) : ‖ratio γ z‖ = 1 := by
  let g : SL(2, ℤ) := γ
  have hS : ‖halfFactor g z‖ ^ (2 : ℕ) =
      ‖UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z‖ := by
    rw [← norm_pow, halfFactor_sq]
  have hSq : ‖jacobiTheta ((γ • z : ℍ) : ℂ)‖ ^ (2 : ℕ) =
      ‖halfFactor g z * jacobiTheta (z : ℂ)‖ ^ (2 : ℕ) := by
    rw [norm_mul, mul_pow, hS]
    exact theta_norm_sq_smul γ z
  have hNorm : ‖jacobiTheta ((γ • z : ℍ) : ℂ)‖ =
      ‖halfFactor g z * jacobiTheta (z : ℂ)‖ := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt hSq
  rw [ratio, mobius_coe, norm_div]
  change ‖jacobiTheta ((γ • z : ℍ) : ℂ)‖ /
    ‖halfFactor g z * jacobiTheta (z : ℂ)‖ = 1
  rw [hNorm, div_self (norm_ne_zero_iff.mpr
    (mul_ne_zero (halfFactor_ne_zero g z) (jacobiTheta_ne_zero_upperHalfPlane z)))]

def phase (γ : GammaTwo) : ℂ := ratio γ Complex.I

theorem phase_norm (γ : GammaTwo) : ‖phase γ‖ = 1 := ratio_norm γ UpperHalfPlane.I

theorem ratio_eq_phase (γ : GammaTwo) (z : ℍ) : ratio γ z = phase γ := by
  let C := UpperHalfPlane.upperHalfPlaneSet
  have hConv : Convex ℝ C :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap
  have hI : Complex.I ∈ C := by simp [C, UpperHalfPlane.upperHalfPlaneSet]
  have hMax : IsMaxOn (norm ∘ ratio γ) C Complex.I := by
    intro τ hτ
    let w : ℍ := ⟨τ, hτ⟩
    change ‖ratio γ w‖ ≤ ‖phase γ‖
    rw [ratio_norm, phase_norm]
  exact Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hConv.isPreconnected
    UpperHalfPlane.isOpen_upperHalfPlaneSet (ratio_differentiable γ) hI hMax z z.im_pos

theorem theta_transformation (γ : GammaTwo) (z : ℍ) :
    jacobiTheta ((γ • z : ℍ) : ℂ) =
      phase γ * halfFactor (γ : SL(2, ℤ)) z * jacobiTheta (z : ℂ) := by
  have h := ratio_eq_phase γ z
  rw [ratio, mobius_coe] at h
  have hQ := (div_eq_iff (mul_ne_zero (halfFactor_ne_zero _ z)
    (jacobiTheta_ne_zero_upperHalfPlane z))).mp h
  simpa only [mul_assoc] using hQ

end
end ManuscriptAudit.ThetaHolomorphicMultiplier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaHolomorphicMultiplier.ratio_norm,
      ``ManuscriptAudit.ThetaHolomorphicMultiplier.phase_norm,
      ``ManuscriptAudit.ThetaHolomorphicMultiplier.ratio_eq_phase,
      ``ManuscriptAudit.ThetaHolomorphicMultiplier.theta_transformation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
