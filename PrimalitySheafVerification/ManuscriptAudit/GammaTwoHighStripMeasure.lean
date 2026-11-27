import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientCutMeasure

/-! Width two above height one is an exact measurable chart of the quotient cusp. -/

namespace ManuscriptAudit.GammaTwoHighStripMeasure

open Function MeasureTheory Set Matrix
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane Pointwise MatrixGroups

noncomputable section

def strip : Set ℍ := {z | 1 < z.im ∧ z.re ∈ Ico (0 : ℝ) 2}

theorem strip_measurable : MeasurableSet strip := by
  exact (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable).inter
    (measurableSet_Ico.preimage UpperHalfPlane.continuous_re.measurable)

private theorem matrix_formula (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + (g 0 1 : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℂ)) := by
  simpa using UpperHalfPlane.coe_specialLinearGroup_apply g z

private theorem matrix_fixes_all_of_high_fixed (g : SL(2, ℤ)) (z : ℍ)
    (hz : 1 < z.im) (hfix : g • z = z) (w : ℍ) : g • w = w := by
  have hc : g 1 0 = 0 := HighInfinityCusp.bottom_left_zero_of_high_image le_rfl g hz
    (hfix.symm ▸ hz)
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  have hs := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet
  have had : g 0 0 = g 1 1 :=
    hs.elim (fun h => h.1.trans h.2.symm) (fun h => h.1.trans h.2.symm)
  have hd : ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
    rcases hs with h | h <;> rw [h.2] <;> norm_num
  have hf := congrArg (fun u : ℍ => (u : ℂ)) hfix
  rw [matrix_formula g z, hc, had] at hf
  simp only [Int.cast_zero, zero_mul, zero_add] at hf
  have hb : g 0 1 = 0 := by
    have h := (div_eq_iff hd).mp hf
    rw [mul_comm (z : ℂ) ((g 1 1 : ℤ) : ℂ)] at h
    have h0 : ((g 0 1 : ℤ) : ℂ) = 0 :=
      add_left_cancel (h.trans (add_zero _).symm)
    exact_mod_cast h0
  apply UpperHalfPlane.coe_inj.mp
  rw [matrix_formula g w, hc, had, hb]
  simp only [Int.cast_zero, zero_mul, add_zero, zero_add]
  exact (div_eq_iff hd).mpr (mul_comm _ _)

theorem effective_fixed_high_eq_one (g : GammaTwoEffective) (z : ℍ)
    (hz : 1 < z.im) (hf : g • z = z) : g = 1 := by
  obtain ⟨γ, hγ⟩ := effective_exists_gamma g
  have hraw : ((γ : SL(2, ℤ)) • z : ℍ) = z := (hγ z).symm.trans hf
  apply Subtype.ext
  apply Equiv.ext
  intro w
  change g • w = (1 : GammaTwoEffective) • w
  rw [hγ w, one_smul]
  exact matrix_fixes_all_of_high_fixed (γ : SL(2, ℤ)) z hz hraw w

theorem strip_pairwise_disjoint : Pairwise (Disjoint on fun g : GammaTwoEffective => g • strip) := by
  rw [pairwise_disjoint_smul_iff]
  intro g hg
  rw [Set.disjoint_left]
  intro z hz hw
  rw [← image_smul] at hz
  obtain ⟨w, hw', hgw⟩ := hz
  obtain ⟨γ, hγ⟩ := effective_exists_gamma g
  have hγw : γ • w = z := (hγ w).symm.trans hgw
  have hH : 1 < z.im := hw.1
  have hH' : 1 < w.im := hw'.1
  obtain ⟨m, hm⟩ := (HighInfinityCusp.high_orbit_iff_even_translate
    le_rfl hH' hH).mp ⟨γ, hγw⟩
  have hre : z.re = w.re + 2 * (m : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hm
  have hlo : (-1 : ℝ) < (m : ℝ) := by linarith only [hre, hw.2.1, hw'.2.2]
  have hhi : (m : ℝ) < 1 := by linarith only [hre, hw.2.2, hw'.2.1]
  have hlo' : (-1 : ℤ) < m := by exact_mod_cast hlo
  have hhi' : m < (1 : ℤ) := by exact_mod_cast hhi
  have hm0 : m = 0 := by omega
  have hz' : z = w := UpperHalfPlane.coe_inj.mp (by simpa [hm0] using hm)
  exact hg (effective_fixed_high_eq_one g w hH' (hgw.trans hz'))

theorem quotient_strip_measure (D : GammaTwoFundamentalDomain) :
    (hyperbolicMeasure.restrict strip).map gammaTwoQuotientMk =
      D.quotientMeasure.restrict (gammaTwoQuotientMk '' strip) :=
  GammaTwoQuotientCutMeasure.map_restrict_eq D strip_measurable strip_pairwise_disjoint

end
end ManuscriptAudit.GammaTwoHighStripMeasure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GammaTwoHighStripMeasure.effective_fixed_high_eq_one,
      ``ManuscriptAudit.GammaTwoHighStripMeasure.strip_pairwise_disjoint,
      ``ManuscriptAudit.GammaTwoHighStripMeasure.quotient_strip_measure] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
