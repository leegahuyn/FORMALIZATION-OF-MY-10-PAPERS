import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfilesNonzero
import PrimalitySheafVerification.ManuscriptAudit.ThetaGammaTwoMetric

/-! The weight-half theta mode defines an actual unitary cocycle on the level-two quotient. -/

namespace ManuscriptAudit.ThetaGlobalSection

open LiteralCuspTruncation ThetaGammaTwoMetric ThetaProfilesNonzero ThetaProfileGenerators
open Matrix
open scoped MatrixGroups UpperHalfPlane

noncomputable section

private theorem direction_zero (g : SL(2, ℤ)) :
    direction g (![0, 0] : Direction) = ![0, 0] := by
  have h : (![0, 0] : Direction) = 0 := by decide
  rw [h]
  simp [direction]

private theorem direction_standard_ne_zero (g : SL(2, ℤ)) :
    direction g (![1, 1] : Direction) ≠ ![0, 0] := by
  intro h
  have he := congrArg (direction g⁻¹) h
  rw [← direction_mul, inv_mul_cancel, direction_one, direction_zero] at he
  exact (by decide : (![1, 1] : Direction) ≠ ![0, 0]) he

private theorem density_aux {z : ℍ} (hz : (2 / 3 : ℝ) < z.im)
    {v : Direction} (hv : v ≠ ![0, 0]) : 0 < profileDensity v z := by
  have h : profile v (z : ℂ) ≠ 0 := by
    rcases direction_cases v with h | h | h | h
    · exact (hv h).elim
    · rw [h, profile_11]
      exact jacobiTheta_ne_zero_at_height hz
    · rw [h, profile_01]
      exact thetaAlternating_ne_zero_at_height hz
    · rw [h, profile_10]
      exact thetaHalfShift_ne_zero_at_height hz
  exact mul_pos (Real.sqrt_pos.mpr z.im_pos) (pow_pos (norm_pos_iff.mpr h) _)

theorem jacobiTheta_ne_zero_upperHalfPlane (z : ℍ) : jacobiTheta (z : ℂ) ≠ 0 := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hHeight : (2 / 3 : ℝ) < (g • z).im := by
    have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    by_contra! he
    nlinarith [mul_nonneg (sub_nonneg.mpr he)
      (show (0 : ℝ) ≤ 2 / 3 + (g • z).im by positivity)]
  have h := density_aux hHeight (direction_standard_ne_zero g)
  have he := full_modular_density_covariance g (direction g (![1, 1] : Direction)) z
  rw [← direction_mul, inv_mul_cancel, direction_one] at he
  change _ = thetaDensity (profile (![1, 1] : Direction)) z at he
  rw [profile_11] at he
  rw [he] at h
  intro hh
  simp [thetaDensity, hh] at h

/-- The genuine quarter-height normalization of the native Jacobi theta. -/
def thetaWeightedMode (z : ℍ) : ℂ :=
  Complex.ofReal (z.im ^ (1 / 4 : ℝ)) * jacobiTheta (z : ℂ)

theorem thetaWeightedMode_ne_zero (z : ℍ) : thetaWeightedMode z ≠ 0 :=
  mul_ne_zero (by
    exact_mod_cast (Real.rpow_pos_of_pos z.im_pos (1 / 4 : ℝ)).ne')
    (jacobiTheta_ne_zero_upperHalfPlane z)

theorem thetaWeightedMode_norm_sq (z : ℍ) :
    ‖thetaWeightedMode z‖ ^ (2 : ℕ) = thetaDensity jacobiTheta z := by
  have h : (z.im ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt z.im := by
    rw [← Real.rpow_two, ← Real.rpow_mul z.im_pos.le, Real.sqrt_eq_rpow]
    norm_num
  rw [thetaWeightedMode, thetaDensity, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le _), h]

/-- The actual unit phase of the weighted section's quotient rule. -/
def thetaUnitaryFactor (γ : GammaTwo) (z : ℍ) : ℂ :=
  thetaWeightedMode (γ • z) / thetaWeightedMode z

theorem thetaUnitaryFactor_norm (γ : GammaTwo) (z : ℍ) :
    ‖thetaUnitaryFactor γ z‖ = 1 := by
  have hSq : ‖thetaWeightedMode (γ • z)‖ ^ (2 : ℕ) = ‖thetaWeightedMode z‖ ^ (2 : ℕ) := by
    rw [thetaWeightedMode_norm_sq, thetaWeightedMode_norm_sq]
    exact thetaDensity_invariant γ.val γ.property z
  have hn := congrArg Real.sqrt hSq
  simp only [Real.sqrt_sq (norm_nonneg _)] at hn
  rw [thetaUnitaryFactor, norm_div, hn,
    div_self (norm_pos_iff.mpr (thetaWeightedMode_ne_zero z)).ne']

theorem thetaUnitaryFactor_cocycle (γ δ : GammaTwo) (z : ℍ) :
    thetaUnitaryFactor (γ * δ) z =
      thetaUnitaryFactor γ (δ • z) * thetaUnitaryFactor δ z := by
  unfold thetaUnitaryFactor
  rw [mul_smul]
  field_simp [thetaWeightedMode_ne_zero z, thetaWeightedMode_ne_zero (δ • z)] <;> ring

theorem thetaWeightedMode_equivariant (γ : GammaTwo) (z : ℍ) :
    thetaWeightedMode (γ • z) = thetaUnitaryFactor γ z * thetaWeightedMode z := by
  rw [thetaUnitaryFactor, div_mul_cancel₀ _ (thetaWeightedMode_ne_zero z)]

end
end ManuscriptAudit.ThetaGlobalSection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaGlobalSection.jacobiTheta_ne_zero_upperHalfPlane,
      ``ManuscriptAudit.ThetaGlobalSection.thetaWeightedMode_norm_sq,
      ``ManuscriptAudit.ThetaGlobalSection.thetaUnitaryFactor_norm,
      ``ManuscriptAudit.ThetaGlobalSection.thetaUnitaryFactor_cocycle,
      ``ManuscriptAudit.ThetaGlobalSection.thetaWeightedMode_equivariant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
