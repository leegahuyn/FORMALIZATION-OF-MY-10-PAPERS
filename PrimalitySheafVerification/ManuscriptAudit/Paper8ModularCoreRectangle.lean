import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Real.Sqrt

/-! A bounded rectangular extension of the modular core uses only the identity and inversion. -/

namespace ManuscriptAudit.Paper8ModularCoreRectangle

open UpperHalfPlane Set
open scoped MatrixGroups

noncomputable section

def coreMinimumHeight : ℝ := Real.sqrt 3 / 2

def modularCoreRectangle (T : ℝ) : Set ℍ :=
  {z | |z.re| ≤ 1 / 2 ∧ coreMinimumHeight ≤ z.im ∧ z.im ≤ T}

theorem coreMinimumHeight_pos : 0 < coreMinimumHeight := by
  unfold coreMinimumHeight
  positivity

private theorem coreMinimumHeight_sq : coreMinimumHeight ^ 2 = 3 / 4 := by
  unfold coreMinimumHeight
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem fd_height_ge_coreMinimum {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    coreMinimumHeight ≤ z.im := by
  change 1 ≤ Complex.normSq (z : ℂ) ∧ |z.re| ≤ 1 / 2 at hz
  have hx : z.re ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hz.2)
  have hn : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two, pow_two]
  have hy : coreMinimumHeight ^ 2 ≤ z.im ^ 2 := by
    rw [coreMinimumHeight_sq]
    nlinarith [hz.1, hn]
  simpa only [abs_of_nonneg coreMinimumHeight_pos.le, abs_of_nonneg z.im_pos.le] using sq_le_sq.mp hy

theorem modular_fd_truncation_subset_rectangle (T : ℝ) :
    ModularGroup.fd ∩ {z : ℍ | z.im ≤ T} ⊆ modularCoreRectangle T := by
  intro z hz
  have hre : |z.re| ≤ 1 / 2 := hz.1.2
  exact ⟨hre, fd_height_ge_coreMinimum hz.1, hz.2⟩

private theorem modular_S_coe (z : ℍ) :
    ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

private theorem modular_S_normSq (z : ℍ) : Complex.normSq (ModularGroup.S • z : ℍ) =
    (Complex.normSq (z : ℂ))⁻¹ := by
  rw [modular_S_coe, Complex.normSq_neg, Complex.normSq_inv]

private theorem modular_S_real (z : ℍ) :
    (ModularGroup.S • z).re = -z.re / Complex.normSq (z : ℂ) := by
  change ((ModularGroup.S • z : ℍ) : ℂ).re = _
  rw [modular_S_coe, Complex.neg_re, Complex.inv_re, UpperHalfPlane.coe_re, neg_div]

private theorem modular_S_imag (z : ℍ) :
    (ModularGroup.S • z).im = z.im / Complex.normSq (z : ℂ) := by
  change ((ModularGroup.S • z : ℍ) : ℂ).im = _
  rw [modular_S_coe, Complex.neg_im, Complex.inv_im, UpperHalfPlane.coe_im, neg_div, neg_neg]

private theorem core_im_sq_lower {z : ℍ} (hz : coreMinimumHeight ≤ z.im) :
    (3 / 4 : ℝ) ≤ z.im ^ 2 := by
  rw [← coreMinimumHeight_sq]
  exact pow_le_pow_left₀ coreMinimumHeight_pos.le hz 2

theorem modular_S_mem_fd_of_core_outside_circle {z : ℍ}
    (hx : |z.re| ≤ 1 / 2) (hy : coreMinimumHeight ≤ z.im)
    (hCircle : Complex.normSq (z : ℂ) < 1) : ModularGroup.S • z ∈ ModularGroup.fd := by
  change 1 ≤ Complex.normSq (ModularGroup.S • z : ℍ) ∧ |(ModularGroup.S • z).re| ≤ 1 / 2
  constructor
  · rw [modular_S_normSq]
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le z.normSq_pos hCircle.le
  · rw [modular_S_real, abs_div, abs_neg, abs_of_pos z.normSq_pos]
    apply (div_le_iff₀ z.normSq_pos).2
    have hY := core_im_sq_lower hy
    have hProd := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr (show |z.re| ≤ 3 / 2 by linarith))
    have hN : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two, pow_two]
    nlinarith [sq_abs z.re]

theorem modular_S_height_le_two_on_core {z : ℍ} (hy : coreMinimumHeight ≤ z.im) :
    (ModularGroup.S • z).im ≤ 2 := by
  rw [modular_S_imag]
  apply (div_le_iff₀ z.normSq_pos).2
  have hY := core_im_sq_lower hy
  have hHalf : (1 / 2 : ℝ) ≤ z.im := by
    apply le_of_not_gt
    intro hz
    have hSq : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 := pow_lt_pow_left₀ hz z.im_pos.le (by decide : 2 ≠ 0)
    norm_num at hSq
    linarith
  have hLow : z.im ≤ 2 * z.im ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHalf) z.im_pos.le]
  have hN : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two, pow_two]
  nlinarith [sq_nonneg z.re]

theorem modularCoreRectangle_cover (T : ℝ) {z : ℍ} (hz : z ∈ modularCoreRectangle T) :
    z ∈ ModularGroup.fd ∩ {w : ℍ | w.im ≤ T} ∨
      ModularGroup.S • z ∈ ModularGroup.fd ∩ {w : ℍ | w.im ≤ 2} := by
  obtain ⟨hx, hy, hT⟩ := hz
  by_cases hC : 1 ≤ Complex.normSq (z : ℂ)
  · exact Or.inl ⟨⟨hC, hx⟩, hT⟩
  · exact Or.inr ⟨modular_S_mem_fd_of_core_outside_circle hx hy (lt_of_not_ge hC),
      modular_S_height_le_two_on_core hy⟩

end
end ManuscriptAudit.Paper8ModularCoreRectangle

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ModularCoreRectangle.modularCoreRectangle_cover
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
