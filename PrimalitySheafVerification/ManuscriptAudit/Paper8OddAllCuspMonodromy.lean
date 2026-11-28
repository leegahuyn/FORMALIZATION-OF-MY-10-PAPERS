import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCuspFloquetPhase

/-! The actual odd half-weight character is nontrivial on a width-four translation at every cusp. -/

namespace ManuscriptAudit.Paper8OddAllCuspMonodromy

open Matrix UpperHalfPlane MaassLaplacian
open Paper8EtaCriticalOddVanishing Paper8EtaCuspWidths Paper8OddCuspFloquetPhase
open Paper8OddCrossCuspRows
open scoped MatrixGroups

noncomputable section

def periodFourPhase : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (4 : ℕ) / 24)

theorem periodFourPhase_ne_one : periodFourPhase ≠ 1 := by
  intro h
  have hDiv := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 4) (N := 24) (by decide)).1 h
  norm_num at hDiv

private theorem widthFour_translation_character (g : SL(2, ℤ)) :
    levelCharacter ⟨g * ModularGroup.T ^ (4 : ℤ) * g⁻¹, conjugatedTranslation_level 4 g⟩ = 1 := by
  have hDet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  have hD : (g * ModularGroup.T ^ (4 : ℤ) * g⁻¹) 1 1 = 1 + g 0 0 * g 1 0 * 4 := by
    change ((g.1 * (ModularGroup.T ^ (4 : ℤ)).1) * (g⁻¹).1) 1 1 = _
    rw [ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hDet
  rw [levelCharacter_apply]
  change chiFour (((g * ModularGroup.T ^ (4 : ℤ) * g⁻¹) 1 1 : ℤ) : ZMod 4) = 1
  rw [hD, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_one]
  rw [show ((4 : ℤ) : ZMod 4) = 0 by decide, mul_zero, add_zero]
  decide

theorem cuspOddProfile_periodFour {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (g : SL(2, ℤ)) (z : ℍ) :
    cuspOddProfile F g (ModularGroup.T ^ (4 : ℤ) • z) =
      periodFourPhase * cuspOddProfile F g z := by
  rw [cuspOddProfile_shift hF g 4 (conjugatedTranslation_level 4 g), widthFour_translation_character,
    Int.cast_one, one_mul, negativePhase_T_pow, periodFourPhase] <;> norm_num

def cuspHorizontalProfile (F : ℂ → ℂ) (g : SL(2, ℤ)) (x y : ℝ) : ℂ :=
  cuspOddProfile F g (ofComplex (complexPoint x y))

theorem cuspHorizontalProfile_floquet {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (g : SL(2, ℤ)) (x y : ℝ) (hy : 0 < y) :
    cuspHorizontalProfile F g (x + 4) y = periodFourPhase * cuspHorizontalProfile F g x y := by
  have hPt (u : ℝ) : 0 < (complexPoint u y).im := by rwa [complexPoint_im]
  have hAction : ModularGroup.T ^ (4 : ℤ) • ofComplex (complexPoint x y) =
      ofComplex (complexPoint (x + 4) y) := by
    rw [UpperHalfPlane.modular_T_zpow_smul, ofComplex_apply_of_im_pos (hPt x),
      ofComplex_apply_of_im_pos (hPt (x + 4))]
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]
    change (((4 : ℝ) : ℂ) + complexPoint x y) = complexPoint (x + 4) y
    unfold complexPoint
    push_cast
    ring
  change cuspOddProfile F g (ofComplex (complexPoint (x + 4) y)) =
    periodFourPhase * cuspOddProfile F g (ofComplex (complexPoint x y))
  rw [← hAction]
  exact cuspOddProfile_periodFour hF g _

theorem cuspHorizontalProfile_no_constant {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (g : SL(2, ℤ)) (x y : ℝ) (hy : 0 < y)
    (hConst : cuspHorizontalProfile F g (x + 4) y = cuspHorizontalProfile F g x y) :
    cuspHorizontalProfile F g x y = 0 := by
  have h := (cuspHorizontalProfile_floquet hF g x y hy).symm.trans hConst
  have hP : (periodFourPhase - 1) * cuspHorizontalProfile F g x y = 0 := by
    rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp hP).resolve_left (sub_ne_zero.mpr periodFourPhase_ne_one)

end
end ManuscriptAudit.Paper8OddAllCuspMonodromy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddAllCuspMonodromy.periodFourPhase_ne_one,
      ``ManuscriptAudit.Paper8OddAllCuspMonodromy.cuspHorizontalProfile_floquet,
      ``ManuscriptAudit.Paper8OddAllCuspMonodromy.cuspHorizontalProfile_no_constant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
