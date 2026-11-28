import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8WeightTwoCosetTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! The native T and S pairings cancel the vertical sides and circular arc of the standard domain. -/

namespace ManuscriptAudit.Paper8StandardDomainSidePairing

open Set MeasureTheory UpperHalfPlane ModularForm MaassLaplacian
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups ModularForm Interval

noncomputable section

theorem weightTwo_T_invariant {f : ℍ → ℂ}
    (hT : f ∣[(2 : ℤ)] ModularGroup.T = f) (z : ℍ) :
    f (ModularGroup.T • z) = f z := by
  have h := (ModularForm.slash_action_eq'_iff 2 f ModularGroup.T z).mp (congrFun hT z)
  change f (ModularGroup.T • z) = denominator ModularGroup.T z ^ (2 : ℤ) * f z at h
  simpa [denominator, ModularGroup.coe_T] using h

theorem weightTwo_S_transform {f : ℍ → ℂ}
    (hS : f ∣[(2 : ℤ)] ModularGroup.S = f) (z : ℍ) :
    f (ModularGroup.S • z) = (z : ℂ) ^ 2 * f z := by
  have h := (ModularForm.slash_action_eq'_iff 2 f ModularGroup.S z).mp (congrFun hS z)
  change f (ModularGroup.S • z) = denominator ModularGroup.S z ^ (2 : ℤ) * f z at h
  rw [denominator_eq, ModularGroup.denom_S, zpow_ofNat] at h
  exact h

def arcHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def arcPoint (x : ℝ) : ℍ := ofComplex (complexPoint x (arcHeight x))

def arcTangent (x : ℝ) : ℂ := ((-Complex.I) / (arcHeight x : ℂ)) * (arcPoint x : ℂ)

theorem arcHeight_neg (x : ℝ) : arcHeight (-x) = arcHeight x := by
  simp [arcHeight]

theorem arcHeight_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < arcHeight x := by
  have hL : 0 ≤ x + 1 / 2 := by linarith [(abs_le.mp hx).1]
  have hR : 0 ≤ 1 / 2 - x := sub_nonneg.mpr (abs_le.mp hx).2
  apply Real.sqrt_pos.2
  nlinarith [mul_nonneg hL hR]

theorem arcPoint_coe {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (arcPoint x : ℂ) = complexPoint x (arcHeight x) := by
  have hIm : 0 < (complexPoint x (arcHeight x)).im := by
    rw [complexPoint_im]
    exact arcHeight_pos hx
  rw [arcPoint, ofComplex_apply_of_im_pos hIm] <;> rfl

private theorem arcPoint_normSq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Complex.normSq (arcPoint x : ℂ) = 1 := by
  have hL : 0 ≤ x + 1 / 2 := by linarith [(abs_le.mp hx).1]
  have hR : 0 ≤ 1 / 2 - x := sub_nonneg.mpr (abs_le.mp hx).2
  have hSq : arcHeight x ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (by nlinarith [mul_nonneg hL hR])
  rw [arcPoint_coe hx, Complex.normSq_apply]
  simp only [complexPoint, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero]
  nlinarith [hSq]

theorem arcPoint_neg_coe {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (arcPoint (-x) : ℂ) = -((arcPoint x : ℂ)⁻¹) := by
  have hx' : |-x| ≤ 1 / 2 := by simpa only [abs_neg] using hx
  rw [Complex.inv_def, arcPoint_normSq hx, inv_one, Complex.ofReal_one, mul_one,
    arcPoint_coe hx, arcPoint_coe hx', arcHeight_neg]
  apply Complex.ext <;> simp [complexPoint, Complex.mul_re, Complex.mul_im]

theorem arcPoint_S {x : ℝ} (hx : |x| ≤ 1 / 2) :
    ModularGroup.S • arcPoint x = arcPoint (-x) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, arcPoint_neg_coe hx]
  simp [inv_neg]

theorem arcHeight_hasDerivAt {x : ℝ} (hx : |x| ≤ 1 / 2) :
    HasDerivAt arcHeight (-x / arcHeight x) x := by
  have hL : 0 ≤ x + 1 / 2 := by linarith [(abs_le.mp hx).1]
  have hR : 0 ≤ 1 / 2 - x := sub_nonneg.mpr (abs_le.mp hx).2
  have hPos : 0 < 1 - x ^ 2 := by nlinarith [mul_nonneg hL hR]
  have hPow : HasDerivAt ((id : ℝ → ℝ) ^ (2 : ℕ)) (2 * x) x := by
    simpa [id_eq] using (hasDerivAt_id x).pow (2 : ℕ)
  have hQuad : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-2 * x) x := by
    rw [neg_mul]
    change HasDerivAt (fun u : ℝ => 1 - ((id : ℝ → ℝ) ^ (2 : ℕ)) u) (-(2 * x)) x
    exact hPow.const_sub 1
  have h := (Real.hasDerivAt_sqrt hPos.ne').comp x hQuad
  change HasDerivAt arcHeight ((1 / (2 * arcHeight x)) * (-2 * x)) x at h
  have hE : (1 / (2 * arcHeight x)) * (-2 * x) = -x / arcHeight x := by
    field_simp [(arcHeight_pos hx).ne'] <;> ring
  rw [hE] at h
  exact h

theorem arcTangent_eq_derivative {x : ℝ} (hx : |x| ≤ 1 / 2) :
    arcTangent x = 1 + Complex.I * ((deriv arcHeight x : ℝ) : ℂ) := by
  let h : ℂ := (arcHeight x : ℂ)
  have hn : h ≠ 0 := Complex.ofReal_ne_zero.mpr (arcHeight_pos hx).ne'
  have hi : -Complex.I * (h * Complex.I) = h := by
    linear_combination (-h) * Complex.I_sq
  rw [arcTangent, arcPoint_coe hx, (arcHeight_hasDerivAt hx).deriv]
  simp only [complexPoint, Complex.ofReal_neg, Complex.ofReal_div]
  change (-Complex.I / h) * ((x : ℂ) + h * Complex.I) = 1 + Complex.I * (-(x : ℂ) / h)
  calc
    _ = ((-Complex.I) * (x : ℂ) + (-Complex.I) * (h * Complex.I)) / h := by ring
    _ = _ := by rw [hi]; field_simp [hn] <;> ring

def arcCurrent (f : ℍ → ℂ) (x : ℝ) : ℂ := arcTangent x * f (arcPoint x)

theorem arcCurrent_odd {f : ℍ → ℂ}
    (hS : f ∣[(2 : ℤ)] ModularGroup.S = f) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    arcCurrent f (-x) = -arcCurrent f x := by
  have hF : f (arcPoint (-x)) = (arcPoint x : ℂ) ^ 2 * f (arcPoint x) := by
    rw [← arcPoint_S hx, weightTwo_S_transform hS]
  have hHt : (arcHeight x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (arcHeight_pos hx).ne'
  unfold arcCurrent arcTangent
  rw [hF, arcPoint_neg_coe hx, arcHeight_neg]
  field_simp [(arcPoint x).ne_zero, hHt] <;> ring

theorem arcCurrent_integral_zero {f : ℍ → ℂ}
    (hS : f ∣[(2 : ℤ)] ModularGroup.S = f) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f x) = 0 := by
  have hA : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hSame :
      (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f (-x)) =
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := (-(1 / 2) : ℝ)) (b := 1 / 2) (arcCurrent f))
  have hNeg :
      (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f (-x)) =
      -(∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f x) := by
    calc
      _ = ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), -arcCurrent f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hA] at hx
        exact arcCurrent_odd hS (abs_le.mpr hx)
      _ = _ := intervalIntegral.integral_neg
  have h := hSame.symm.trans hNeg
  have hZero : (2 : ℂ) * (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f x) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hZero).resolve_left (by norm_num)

end
end ManuscriptAudit.Paper8StandardDomainSidePairing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.weightTwo_T_invariant,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.weightTwo_S_transform,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.arcPoint_S,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.arcHeight_hasDerivAt,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.arcTangent_eq_derivative,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.arcCurrent_odd,
      ``ManuscriptAudit.Paper8StandardDomainSidePairing.arcCurrent_integral_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
