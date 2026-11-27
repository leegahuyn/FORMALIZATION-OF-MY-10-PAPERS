import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassRectangleAdjoint

/-! Exact nonnegative energy identity and spectral lower bound for the bounded cusp rectangle. -/

namespace ManuscriptAudit.Paper8MaassRectangleEnergy

open MeasureTheory Set
open MaassLaplacian Paper8NegativeHalfMaassFactorization
open Paper8MaassRectangleAdjoint RectangularIntegral

noncomputable section

def normSquare (a b c d : ℝ) (F : Profile) : ℝ :=
  (box a b c d (density F F)).re

private theorem continuous_self_density {a b c d : ℝ} (hc : 0 < c) {F : Profile}
    (hF : ContinuousOn F.uncurry (rectangle a b c d)) :
    ContinuousOn (density F F) (rectangle a b c d) := by
  have hy : ContinuousOn (fun z : ℝ × ℝ => (z.2 : ℂ)) (rectangle a b c d) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hFc := Complex.conjCLE.continuous.comp_continuousOn hF
  apply (hFc.mul hF).div (hy.pow 2)
  intro z hz
  exact pow_ne_zero 2 (by exact_mod_cast (hc.trans_le hz.2.1).ne')

private theorem re_self_density (F : Profile) (z : ℝ × ℝ) :
    (density F F z).re = ‖F z.1 z.2‖ ^ 2 / z.2 ^ 2 := by
  unfold density
  have hStar : star (F z.1 z.2) * F z.1 z.2 = (↑(‖F z.1 z.2‖ ^ 2 : ℝ) : ℂ) :=
    Complex.conj_mul' (F z.1 z.2)
  rw [hStar, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

private theorem normSquare_eq_integral {a b c d : ℝ} (hc : 0 < c) (F : Profile)
    (hF : ContinuousOn F.uncurry (rectangle a b c d)) :
    normSquare a b c d F = ∫ z in rectangle a b c d, (density F F z).re := by
  unfold normSquare box
  exact (Complex.reCLM.integral_comp_comm
    (continuous_integrable (continuous_self_density hc hF))).symm

theorem normSquare_nonnegative {a b c d : ℝ} (hc : 0 < c) (F : Profile)
    (hF : ContinuousOn F.uncurry (rectangle a b c d)) :
    0 ≤ normSquare a b c d F := by
  rw [normSquare_eq_integral hc F hF]
  apply setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
  intro z _
  rw [re_self_density]
  positivity

theorem normSquare_positive {a b c d : ℝ} (hc : 0 < c) (F : Profile)
    (hF : Continuous F.uncurry) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d)
    (hnz : F x y ≠ 0) :
    0 < normSquare a b c d F := by
  let g : ℝ × ℝ → ℝ := fun z => (density F F z).re
  have hg : ContinuousOn g (rectangle a b c d) :=
    Complex.continuous_re.comp_continuousOn (continuous_self_density hc hF.continuousOn)
  have hg₀ : 0 ≤ᵐ[volume.restrict (rectangle a b c d)] g :=
    Filter.Eventually.of_forall (fun z => by
      change 0 ≤ (density F F z).re
      rw [re_self_density]
      positivity)
  let U := (Ioo a b ×ˢ Ioo c d) ∩ (F.uncurry ⁻¹' ({0} : Set ℂ)ᶜ)
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).inter
    (isClosed_singleton.isOpen_compl.preimage hF)
  have hPoint : (x, y) ∈ U := ⟨⟨hx, hy⟩, hnz⟩
  have hSub : U ⊆ Function.support g ∩ rectangle a b c d := by
    intro z hz
    obtain ⟨⟨hxz, hyz⟩, hFz⟩ := hz
    have hnz' : F z.1 z.2 ≠ 0 := hFz
    have hgz : 0 < g z := by
      change 0 < (density F F z).re
      rw [re_self_density]
      exact div_pos (pow_pos (norm_pos_iff.mpr hnz') _) (pow_pos (hc.trans hyz.1) _)
    exact ⟨hgz.ne', ⟨Ioo_subset_Icc_self hxz, Ioo_subset_Icc_self hyz⟩⟩
  rw [normSquare_eq_integral hc F hF.continuousOn,
    setIntegral_pos_iff_support_of_nonneg_ae hg₀ (continuous_integrable hg)]
  exact (hU.measure_pos volume ⟨(x, y), hPoint⟩).trans_le (measure_mono hSub)

theorem spectral_equation_for_raising (F : Profile) (x y λ : ℝ)
    (hx : DifferentiableAt ℝ (fun t => F t y) x)
    (hy : DifferentiableAt ℝ (F x) y)
    (hxx : DifferentiableAt ℝ (fun t => partialX F t y) x)
    (hxy : DifferentiableAt ℝ (partialX F x) y)
    (hyx : DifferentiableAt ℝ (fun t => partialY F t y) x)
    (hyy : DifferentiableAt ℝ (partialY F x) y)
    (hMixed : partialX (partialY F) x y = partialY (partialX F) x y)
    (hEigen : maassDelta (-1/2) F x y = (λ : ℂ) * F x y) :
    adjointExpression (raising F) x y = ((λ - 3/16 : ℝ) : ℂ) * F x y := by
  rw [factorization F x y hx hy hxx hxy hyx hyy hMixed] at hEigen
  push_cast
  linear_combination hEigen

/-- Under the actual Green identity, an eigenfunction's raising energy is its mass
times the spectral parameter shifted by 3/16. -/
theorem eigenvalue_energy {a b c d : ℝ} (F : Profile) (λ : ℝ)
    (hGreen : box a b c d (density F (adjointExpression (raising F))) =
      box a b c d (density (raising F) (raising F)))
    (hEquation : ∀ z ∈ rectangle a b c d,
      adjointExpression (raising F) z.1 z.2 = ((λ - 3/16 : ℝ) : ℂ) * F z.1 z.2) :
    normSquare a b c d (raising F) = (λ - 3/16) * normSquare a b c d F := by
  have hEq : box a b c d (density F (adjointExpression (raising F))) =
      ((λ - 3/16 : ℝ) : ℂ) * box a b c d (density F F) := by
    calc
      box a b c d (density F (adjointExpression (raising F))) =
          box a b c d (fun z => ((λ - 3/16 : ℝ) : ℂ) * density F F z) := by
        apply box_congr
        intro z hz
        unfold density
        rw [hEquation z hz]
        ring
      _ = _ := by
        unfold box
        exact integral_const_mul _ _
  rw [hGreen] at hEq
  exact by simpa only [normSquare, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using congrArg Complex.re hEq

theorem spectral_lower_bound {a b c d : ℝ} (hc : 0 < c) (F : Profile) (λ : ℝ)
    (hRaise : ContinuousOn (raising F).uncurry (rectangle a b c d))
    (hMass : 0 < normSquare a b c d F)
    (hGreen : box a b c d (density F (adjointExpression (raising F))) =
      box a b c d (density (raising F) (raising F)))
    (hEquation : ∀ z ∈ rectangle a b c d,
      adjointExpression (raising F) z.1 z.2 = ((λ - 3/16 : ℝ) : ℂ) * F z.1 z.2) :
    3/16 ≤ λ := by
  have h := normSquare_nonnegative hc (raising F) hRaise
  rw [eigenvalue_energy F λ hGreen hEquation] at h
  by_contra! hlt
  exact (mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hMass).not_ge h

end
end ManuscriptAudit.Paper8MaassRectangleEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8MaassRectangleEnergy.normSquare_nonnegative,
      ``ManuscriptAudit.Paper8MaassRectangleEnergy.normSquare_positive,
      ``ManuscriptAudit.Paper8MaassRectangleEnergy.spectral_equation_for_raising,
      ``ManuscriptAudit.Paper8MaassRectangleEnergy.eigenvalue_energy,
      ``ManuscriptAudit.Paper8MaassRectangleEnergy.spectral_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
