import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaHalfWeightPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPeterssonMass

/-! The actual Dedekind eta supplies the nonzero positive-weight eigenfunction and its Petersson density. -/

namespace ManuscriptAudit.Paper8EtaMaassEigenfunction

open UpperHalfPlane MeasureTheory
open MaassLaplacian Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase
open scoped MatrixGroups ENNReal

noncomputable section

def etaMaass (z : ℍ) : ℂ := (z.im ^ (1 / 4 : ℝ) : ℝ) * ModularForm.eta z

theorem etaMaass_ne_zero (z : ℍ) : etaMaass z ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos z.im_pos _).ne')
    (ModularForm.eta_ne_zero z.im_pos)

theorem etaMaass_laplacian (x y : ℝ) (hy : 0 < y) :
    maassDelta (1 / 2) (weighted (1 / 4) ModularForm.eta) x y =
      (3 / 16 : ℂ) * weighted (1 / 4) ModularForm.eta x y := by
  have h := delta_weighted ModularForm.eta (1 / 4) x y hy
    (fun _ hz => ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz)
  norm_num [Complex.ofReal_div] at h ⊢
  exact h

theorem etaMaass_profile (x y : ℝ) (hy : 0 < y) :
    etaMaass ⟨complexPoint x y, by simpa only [complexPoint_im] using hy⟩ =
      weighted (1 / 4) ModularForm.eta x y := by
  change ((complexPoint x y).im ^ (1 / 4 : ℝ) : ℝ) * ModularForm.eta (complexPoint x y) = _
  rw [complexPoint_im] <;> rfl

private theorem quarter_height_transform (g : SL(2, ℤ)) (z : ℍ) :
    (g • z : ℍ).im ^ (1 / 4 : ℝ) * Real.sqrt ‖denominator g z‖ = z.im ^ (1 / 4 : ℝ) := by
  let d := ‖denominator g z‖
  have hd : 0 < d := norm_pos_iff.mpr (denominator_ne_zero g z)
  have hExp : ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 / 2 := by norm_num
  rw [ModularGroup.im_smul_eq_div_normSq, ← denominator_eq, Complex.normSq_eq_norm_sq,
    Real.div_rpow z.im_pos.le (sq_nonneg d), ← Real.rpow_natCast_mul hd.le 2 (1 / 4 : ℝ),
    hExp, Real.sqrt_eq_rpow]
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hd _).ne'

theorem etaMaass_transform (g : SL(2, ℤ)) (z : ℍ) :
    etaMaass (g • z) = positivePhase g z * etaMaass z := by
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have hHeight : (((g • z : ℍ).im ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      (Real.sqrt ‖denominator g z‖ : ℂ) = ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul] using
      congrArg Complex.ofReal (quarter_height_transform g z)
  unfold etaMaass positivePhase
  rw [← hHeight]
  field_simp [ModularForm.eta_ne_zero z.im_pos, Complex.ofReal_ne_zero.mpr hD.ne'] <;> ring

theorem etaMaass_norm_sq (z : ℍ) :
    ‖etaMaass z‖ ^ 2 = ‖ModularForm.eta z‖ ^ 2 * Real.sqrt z.im := by
  have hExp : (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 := by norm_num
  simp only [etaMaass, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le _),
    mul_pow, ← Real.rpow_mul_natCast z.im_pos.le _ 2, hExp, Real.sqrt_eq_rpow]
  exact mul_comm _ _

theorem etaMaass_mass (S : Set ℍ) :
    (∫⁻ z in S, ENNReal.ofReal (‖etaMaass z‖ ^ 2)) = Paper8EtaPeterssonMass.mass S := by
  unfold Paper8EtaPeterssonMass.mass Paper8EtaPeterssonMass.density
  simp only [etaMaass_norm_sq]

end
end ManuscriptAudit.Paper8EtaMaassEigenfunction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_ne_zero,
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_laplacian,
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_profile,
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_transform,
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_norm_sq,
      ``ManuscriptAudit.Paper8EtaMaassEigenfunction.etaMaass_mass] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
