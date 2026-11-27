import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrincipalThetaScales

/-! The actual principal level-four theta inverts with two different theta scales. -/

namespace ManuscriptAudit.Paper9PrincipalThetaExactInversion

open Complex Paper9PrincipalThetaStrip Paper9PrincipalThetaScales
open scoped UpperHalfPlane MatrixGroups Pointwise

noncomputable section

private theorem standard_inversion (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  have h := jacobiTheta_S_smul (⟨τ, hτ⟩ : ℍ)
  simpa only [UpperHalfPlane.modular_S_smul, neg_div, one_div] using h

theorem principalTheta_actual_inversion (τ : ℂ) (hτ : 0 < τ.im) :
    principalTheta (-1 / τ) =
      (-Complex.I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ -
        (-Complex.I * (τ / 4)) ^ (1 / 2 : ℂ) * jacobiTheta (τ / 4) := by
  let z : ℍ := ⟨τ, hτ⟩
  have hS : 0 < (-1 / τ).im := by
    have h := (ModularGroup.S • z : ℍ).im_pos
    change 0 < ((ModularGroup.S • z : ℍ) : ℂ).im at h
    simpa only [UpperHalfPlane.modular_S_smul, neg_div, one_div, z] using h
  have hFour : 0 < (τ / 4).im := by
    have he : τ / 4 = ((1 / 4 : ℝ) : ℂ) * τ := by push_cast; ring
    rw [he, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  have hne : τ ≠ 0 := fun h => by simpa [h] using hτ
  have hs : (4 : ℂ) * (-1 / τ) = -1 / (τ / 4) := by
    field_simp [hne] <;> ring
  rw [principalTheta_eq_difference _ hS, hs, standard_inversion τ hτ,
    standard_inversion (τ / 4) hFour]

end
end ManuscriptAudit.Paper9PrincipalThetaExactInversion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9PrincipalThetaExactInversion.principalTheta_actual_inversion
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
