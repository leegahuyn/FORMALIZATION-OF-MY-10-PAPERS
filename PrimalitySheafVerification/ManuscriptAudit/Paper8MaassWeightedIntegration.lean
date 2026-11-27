import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination

/-! Complex-valued integration by parts with the two cusp weights. -/

namespace ManuscriptAudit.Paper8MaassWeightedIntegration

open MeasureTheory Set

noncomputable section

theorem weighted_parts {a b : ℝ} (f f' g g' w w' : ℝ → ℂ)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t)
    (hw : ∀ t ∈ uIcc a b, HasDerivAt w (w' t) t)
    (hf' : ContinuousOn f' (uIcc a b)) (hg' : ContinuousOn g' (uIcc a b))
    (hw' : ContinuousOn w' (uIcc a b)) :
    (∫ t in a..b, star (f t)*g' t*w t) =
      star (f b)*g b*w b - star (f a)*g a*w a -
        (∫ t in a..b, star (f' t)*g t*w t) -
        (∫ t in a..b, star (f t)*g t*w' t) := by
  let F : ℝ → ℂ := fun t => star (f' t)*g t*w t
  let G : ℝ → ℂ := fun t => star (f t)*g' t*w t
  let W : ℝ → ℂ := fun t => star (f t)*g t*w' t
  let flux : ℝ → ℂ := fun t => star (f t)*g t*w t
  have hfC : ContinuousOn (fun t => star (f t)) (uIcc a b) :=
    Complex.conjCLE.continuous.comp_continuousOn (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
  have hgC : ContinuousOn g (uIcc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hwC : ContinuousOn w (uIcc a b) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
  have hf'C : ContinuousOn (fun t => star (f' t)) (uIcc a b) :=
    Complex.conjCLE.continuous.comp_continuousOn hf'
  have iF : IntervalIntegrable F volume a b := ((hf'C.mul hgC).mul hwC).intervalIntegrable
  have iG : IntervalIntegrable G volume a b := ((hfC.mul hg').mul hwC).intervalIntegrable
  have iW : IntervalIntegrable W volume a b := ((hfC.mul hgC).mul hw').intervalIntegrable
  have hFlux (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt flux (F t+G t+W t) t := by
    have hc : HasDerivAt (fun y => star (f y)) (star (f' t)) t :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t (hf t ht)
    have h := (hc.mul (hg t ht)).mul (hw t ht)
    change HasDerivAt flux
      ((star (f' t)*g t + star (f t)*g' t)*w t + (star (f t)*g t)*w' t) t at h
    simpa only [add_mul, F, G, W] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hFlux ((iF.add iG).add iW)
  change (∫ t in a..b, F t+G t+W t) = flux b-flux a at h
  rw [intervalIntegral.integral_add (iF.add iG) iW, intervalIntegral.integral_add iF iG] at h
  change (∫ t in a..b, G t) = flux b-flux a - (∫ t in a..b, F t) - (∫ t in a..b, W t)
  linear_combination h


/-- The vertical derivative's actual formal adjoint with hyperbolic density. -/
theorem vertical_adjoint {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f f' g g' : ℝ → ℂ)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t)
    (hf' : ContinuousOn f' (uIcc a b)) (hg' : ContinuousOn g' (uIcc a b))
    (hBdy : star (f b)*g b/(b : ℂ) = star (f a)*g a/(a : ℂ)) :
    (∫ t in a..b, star (f t)*((t : ℂ)*g' t)/(t : ℂ)^2) =
      ∫ t in a..b, star (-(t : ℂ)*f' t+f t)*g t/(t : ℂ)^2 := by
  let w : ℝ → ℂ := fun t => (t : ℂ)⁻¹
  let w' : ℝ → ℂ := fun t => -((t : ℂ)^2)⁻¹
  have hT (t : ℝ) (ht : t ∈ uIcc a b) : (t : ℂ) ≠ 0 := by
    rw [uIcc_of_le hab] at ht
    exact_mod_cast (ha.trans_le ht.1).ne'
  have hW (t : ℝ) (ht : t ∈ uIcc a b) : HasDerivAt w (w' t) t := by
    have htR : t ≠ 0 := by exact_mod_cast hT t ht
    have h := ((hasDerivAt_id t).inv htR).ofReal_comp
    simpa [w, w', div_eq_mul_inv, neg_mul, Complex.ofReal_inv, Complex.ofReal_pow] using h
  have hWC : ContinuousOn w (uIcc a b) := fun t ht => (hW t ht).continuousAt.continuousWithinAt
  have hW'C : ContinuousOn w' (uIcc a b) :=
    ((Complex.continuous_ofReal.pow 2).continuousOn.inv₀
      (fun t ht => pow_ne_zero 2 (hT t ht))).neg
  have hParts := weighted_parts f f' g g' w w' hf hg hW hf' hg' hW'C
  have hBd : star (f b)*g b*w b - star (f a)*g a*w a = 0 := by
    simpa [w, div_eq_mul_inv] using sub_eq_zero.mpr hBdy
  rw [hBd, zero_sub] at hParts
  have hL : (∫ t in a..b, star (f t)*((t : ℂ)*g' t)/(t : ℂ)^2) =
      ∫ t in a..b, star (f t)*g' t*w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold w
    field_simp [hT t ht] <;> ring
  have hR : (∫ t in a..b, star (-(t : ℂ)*f' t+f t)*g t/(t : ℂ)^2) =
      ∫ t in a..b, -(star (f' t)*g t*w t) - star (f t)*g t*w' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change star (-(t : ℂ)*f' t+f t)*g t/(t : ℂ)^2 =
      -(star (f' t)*g t*w t) - star (f t)*g t*w' t
    have hStar : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    simp only [star_add, star_mul, star_neg, hStar, w, w']
    field_simp [hT t ht] <;> ring
  have hFc : ContinuousOn (fun t => star (f t)) (uIcc a b) :=
    Complex.conjCLE.continuous.comp_continuousOn (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
  have hF'c : ContinuousOn (fun t => star (f' t)) (uIcc a b) :=
    Complex.conjCLE.continuous.comp_continuousOn hf'
  have hGc : ContinuousOn g (uIcc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  let F : ℝ → ℂ := fun t => star (f' t)*g t*w t
  let A : ℝ → ℂ := fun t => star (f t)*g t*w' t
  have hF : IntervalIntegrable F volume a b := ((hF'c.mul hGc).mul hWC).intervalIntegrable
  have hA : IntervalIntegrable A volume a b := ((hFc.mul hGc).mul hW'C).intervalIntegrable
  rw [hL, hR]
  have hInt : (∫ t in a..b, -F t - A t) =
      (∫ t in a..b, -F t) - ∫ t in a..b, A t :=
    intervalIntegral.integral_sub hF.neg hA
  rw [intervalIntegral.integral_neg] at hInt
  exact hParts.trans hInt.symm

/-- The horizontal derivative times an imaginary scalar is its actual periodic formal adjoint. -/
theorem horizontal_adjoint {a b : ℝ} (f f' g g' : ℝ → ℂ) (c : ℂ)
    (hc : star c = -c)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t)
    (hf' : ContinuousOn f' (uIcc a b)) (hg' : ContinuousOn g' (uIcc a b))
    (hBdy : star (f b)*g b = star (f a)*g a) :
    (∫ t in a..b, star (f t)*(c*g' t)) = ∫ t in a..b, star (c*f' t)*g t := by
  have h := weighted_parts f f' g g' (fun _ => 1) (fun _ => 0) hf hg
    (fun t _ => hasDerivAt_const t (1 : ℂ)) hf' hg' continuousOn_const
  simp only [mul_one, mul_zero, intervalIntegral.integral_zero, sub_zero, hBdy, sub_self,
    zero_sub] at h
  calc
    (∫ t in a..b, star (f t)*(c*g' t)) =
        c*(∫ t in a..b, star (f t)*g' t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = star c*(∫ t in a..b, star (f' t)*g t) := by rw [h, hc]; ring
    _ = ∫ t in a..b, star (c*f' t)*g t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change star c * (star (f' t) * g t) = star (c * f' t) * g t
      rw [star_mul]
      ring


end
end ManuscriptAudit.Paper8MaassWeightedIntegration

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8MaassWeightedIntegration.weighted_parts,
      ``ManuscriptAudit.Paper8MaassWeightedIntegration.vertical_adjoint,
      ``ManuscriptAudit.Paper8MaassWeightedIntegration.horizontal_adjoint] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
