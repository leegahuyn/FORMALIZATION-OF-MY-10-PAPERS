import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombDirichletMode

/-! The nonzero-boundary residual also solves the weak Dirichlet correction
equation on the genuine width-two cusp collar. -/

namespace ManuscriptAudit.Paper10CoulombDirichletWeak

open MeasureTheory Set
open Paper10CoulombDirichletMode
open Paper10CoulombMultiplier (ScalarField)
open SmoothGaugeCurvature (partialX partialY)
open scoped ContDiff Interval

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def flux (f : ScalarField) (x y : ℝ) : ℝ :=
  Real.sin (Real.pi * x) * deriv v y * f x y

private def horizontal (f : ScalarField) (x y : ℝ) : ℝ :=
  (Paper10CoulombDirichletMode.residual x y).1 * partialX f x y

private def vertical (f : ScalarField) (x y : ℝ) : ℝ :=
  (Paper10CoulombDirichletMode.residual x y).2 * partialY f x y

private theorem derivative_v_continuous : Continuous (deriv v) :=
  (show ContDiff ℝ ∞ (deriv v) from ContDiff.deriv' (by simpa using v_smooth)).continuous

private theorem residual_dx (x y : ℝ) :
    HasDerivAt (fun z ↦ (Paper10CoulombDirichletMode.residual z y).1) (Real.sin (Real.pi*x) * deriv v y) x := by
  have h := (((Real.hasDerivAt_cos (Real.pi * x)).comp x
    ((hasDerivAt_id x).const_mul Real.pi)).mul_const (deriv v y / Real.pi)).neg
  have hd : -(-Real.sin (Real.pi*x) * (Real.pi*1) * (deriv v y / Real.pi)) =
      Real.sin (Real.pi*x) * deriv v y := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [← hd]
  exact h

private theorem residual_dy (x y : ℝ) :
    HasDerivAt (fun z ↦ (Paper10CoulombDirichletMode.residual x z).2) (-(Real.sin (Real.pi*x) * deriv v y)) y :=
  (((v_smooth.differentiable (by simp) y).hasDerivAt).const_mul (Real.sin (Real.pi * x))).neg

private theorem residual_continuous :
    Continuous (fun p : ℝ × ℝ ↦ Paper10CoulombDirichletMode.residual p.1 p.2) := chart_smooth.2.1.continuous

private theorem flux_continuous (f : ScalarField) (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (flux f)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_fst)).mul
    (derivative_v_continuous.comp continuous_snd)).mul hf

private theorem horizontal_continuous (f : ScalarField)
    (hx : Continuous (Function.uncurry (partialX f))) :
    Continuous (Function.uncurry (horizontal f)) := residual_continuous.fst.mul hx

private theorem vertical_continuous (f : ScalarField)
    (hy : Continuous (Function.uncurry (partialY f))) :
    Continuous (Function.uncurry (vertical f)) := residual_continuous.snd.mul hy

private theorem swap_continuous (g : ScalarField) (hg : Continuous (Function.uncurry g)) :
    (∫ y : ℝ in 4..6, ∫ x : ℝ in 0..2, g x y) =
      ∫ x : ℝ in 0..2, ∫ y : ℝ in 4..6, g x y := by
  have h : IntegrableOn (Function.uncurry g) (uIoc (0:ℝ) 2 ×ˢ uIoc (4:ℝ) 6) := by
    apply IntegrableOn.mono_set
      (hg.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc))
    exact Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  exact (intervalIntegral_intervalIntegral_swap h).symm

private theorem integral_horizontal (f : ScalarField)
    (hf : Continuous (Function.uncurry f))
    (hX : ∀ x y, DifferentiableAt ℝ (fun z ↦ f z y) x)
    (hx : Continuous (Function.uncurry (partialX f)))
    (hPeriod : ∀ y, f 2 y = f 0 y) (y : ℝ) :
    (∫ x : ℝ in 0..2, horizontal f x y) = -(∫ x : ℝ in 0..2, flux f x y) := by
  have hc : Continuous (fun x : ℝ ↦ Real.sin (Real.pi*x) * deriv v y) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul continuous_const
  have hd : Continuous (fun x ↦ partialX f x y) := hx.comp (continuous_id.prodMk continuous_const)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := (2 : ℝ))
    (fun x _ ↦ residual_dx x y) (fun x _ ↦ (hX x y).hasDerivAt)
    (hc.intervalIntegrable (μ := volume) _ _) (hd.intervalIntegrable (μ := volume) _ _)
  have hb : (Paper10CoulombDirichletMode.residual 2 y).1 = (Paper10CoulombDirichletMode.residual 0 y).1 := by
    have hR := (periodic 0 y 1).2.1
    norm_num at hR
    exact congrArg Prod.fst hR
  change (∫ x : ℝ in 0..2, horizontal f x y) =
    (Paper10CoulombDirichletMode.residual 2 y).1 * f 2 y - (Paper10CoulombDirichletMode.residual 0 y).1 * f 0 y - (∫ x : ℝ in 0..2, flux f x y) at h
  rw [hb, hPeriod, sub_self, zero_sub] at h
  exact h

private theorem integral_vertical (f : ScalarField)
    (hY : ∀ x y, DifferentiableAt ℝ (f x) y)
    (hy : Continuous (Function.uncurry (partialY f)))
    (hTrace : ∀ x, f x 6 = 0) (x : ℝ) :
    (∫ y : ℝ in 4..6, vertical f x y) = ∫ y : ℝ in 4..6, flux f x y := by
  have hc : Continuous (fun y ↦ -(Real.sin (Real.pi*x) * deriv v y)) :=
    (continuous_const.mul derivative_v_continuous).neg
  have hd : Continuous (fun y ↦ partialY f x y) := hy.comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (4 : ℝ)) (b := (6 : ℝ))
    (fun y _ ↦ residual_dy x y) (fun y _ ↦ (hY x y).hasDerivAt)
    (hc.intervalIntegrable (μ := volume) _ _) (hd.intervalIntegrable (μ := volume) _ _)
  have hb : (Paper10CoulombDirichletMode.residual x 4).2 = 0 :=
    congrArg Prod.snd (zero_below_cusp_band x 4 (by norm_num)).2.1
  change (∫ y : ℝ in 4..6, vertical f x y) =
    (Paper10CoulombDirichletMode.residual x 6).2 * f x 6 - (Paper10CoulombDirichletMode.residual x 4).2 * f x 4 -
      (∫ y : ℝ in 4..6, -(Real.sin (Real.pi*x) * deriv v y) * f x y) at h
  have hr : (fun y ↦ -(Real.sin (Real.pi*x) * deriv v y) * f x y) =
      (fun y ↦ -(flux f x y)) := by
    funext y
    exact neg_mul _ _
  rw [hTrace, hb, mul_zero, zero_mul, sub_self, zero_sub, hr,
    intervalIntegral.integral_neg, neg_neg] at h
  exact h

/-- The hyperbolic inner product density of two one-forms on the collar
equals the Euclidean coefficient pairing times dx dy. -/
def weakPair (f : ScalarField) : ℝ :=
  (∫ x : ℝ in 0..2, ∫ y : ℝ in 4..6, horizontal f x y) +
    ∫ x : ℝ in 0..2, ∫ y : ℝ in 4..6, vertical f x y

/-- The actual residual is orthogonal to every smooth periodic Dirichlet
gradient test. No condition is required at the lower artificial edge of
the collar since the residual already vanishes there. -/
theorem weakPair_eq_zero (f : ScalarField)
    (hf : Continuous (Function.uncurry f))
    (hX : ∀ x y, DifferentiableAt ℝ (fun z ↦ f z y) x)
    (hY : ∀ x y, DifferentiableAt ℝ (f x) y)
    (hx : Continuous (Function.uncurry (partialX f)))
    (hy : Continuous (Function.uncurry (partialY f)))
    (hPeriod : ∀ y, f 2 y = f 0 y) (hTrace : ∀ x, f x 6 = 0) :
    weakPair f = 0 := by
  unfold weakPair
  rw [← swap_continuous (horizontal f) (horizontal_continuous f hx)]
  simp_rw [integral_horizontal f hf hX hx hPeriod, integral_vertical f hY hy hTrace]
  rw [intervalIntegral.integral_neg, swap_continuous (flux f) (flux_continuous f hf),
    neg_add_cancel]

end
end ManuscriptAudit.Paper10CoulombDirichletWeak

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10CoulombDirichletWeak.weakPair_eq_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
