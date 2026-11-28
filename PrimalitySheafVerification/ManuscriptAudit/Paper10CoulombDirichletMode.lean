import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest

/-! A smooth width-two cusp mode gives a Dirichlet gauge potential whose
correction leaves the full zero-trace Coulomb slice. -/

namespace ManuscriptAudit.Paper10CoulombDirichletMode

open Paper10CoulombMultiplier Paper10CoulombProductRule
open SmoothGaugeCurvature (partialX partialY)
open scoped ContDiff Topology

noncomputable section

/-- This switch vanishes below height five and is identically one above 11/2. -/
def cutoff (y : ℝ) : ℝ := Real.smoothTransition (2 * (y - 5))

private def t (y : ℝ) : ℝ := Real.pi * (y - 6)
private def s (y : ℝ) : ℝ := (Real.exp (t y) - Real.exp (-t y)) / (2 * Real.pi)
private def c (y : ℝ) : ℝ := (Real.exp (t y) + Real.exp (-t y)) / 2

private theorem t_deriv (y : ℝ) : HasDerivAt t Real.pi y := by
  simpa only [t, mul_one] using ((hasDerivAt_id y).sub_const 6).const_mul Real.pi

private theorem s_deriv (y : ℝ) : HasDerivAt s (c y) y := by
  have hp := (Real.hasDerivAt_exp (t y)).comp y (t_deriv y)
  have hm := (Real.hasDerivAt_exp (-t y)).comp y (t_deriv y).neg
  have q : (Real.exp (t y) * Real.pi - Real.exp (-t y) * -Real.pi) /
      (2 * Real.pi) = c y := by
    unfold c
    field_simp [Real.pi_ne_zero] <;> ring
  rw [← q]
  exact (hp.sub hm).div_const (2 * Real.pi)

private theorem c_deriv (y : ℝ) : HasDerivAt c (Real.pi ^ 2 * s y) y := by
  have hp := (Real.hasDerivAt_exp (t y)).comp y (t_deriv y)
  have hm := (Real.hasDerivAt_exp (-t y)).comp y (t_deriv y).neg
  have q : (Real.exp (t y) * Real.pi + Real.exp (-t y) * -Real.pi) / 2 =
      Real.pi ^ 2 * s y := by
    unfold s
    field_simp [Real.pi_ne_zero] <;> ring
  rw [← q]
  exact (hp.add hm).div_const 2

def u (y : ℝ) : ℝ := cutoff y * s y
def v (y : ℝ) : ℝ := cutoff y * c y

private theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

private theorem t_smooth : ContDiff ℝ ∞ t :=
  contDiff_const.mul (contDiff_id.sub contDiff_const)

theorem u_smooth : ContDiff ℝ ∞ u :=
  cutoff_smooth.mul (((Real.contDiff_exp.comp t_smooth).sub
    (Real.contDiff_exp.comp t_smooth.neg)).div_const _)

theorem v_smooth : ContDiff ℝ ∞ v :=
  cutoff_smooth.mul (((Real.contDiff_exp.comp t_smooth).add
    (Real.contDiff_exp.comp t_smooth.neg)).div_const _)

def potential : ScalarField := fun x y ↦ Real.sin (Real.pi * x) * u y

def gradient : OneForm := fun x y ↦
  (Real.cos (Real.pi * x) * (Real.pi * u y), Real.sin (Real.pi * x) * deriv u y)

/-- The residual is the rotated derivative of a genuine periodic stream function. -/
def residual : OneForm := fun x y ↦
  (-(Real.cos (Real.pi * x) * (deriv v y / Real.pi)), -(Real.sin (Real.pi * x) * v y))

def inputForm : OneForm := fun x y ↦
  ((gradient x y).1 + (residual x y).1, (gradient x y).2 + (residual x y).2)

theorem gradient_eq_partials (x y : ℝ) :
    gradient x y = (partialX potential x y, partialY potential x y) := by
  have hx := ((Real.hasDerivAt_sin (Real.pi * x)).comp x
    ((hasDerivAt_id x).const_mul Real.pi)).mul_const (u y)
  have hy := ((u_smooth.differentiable (by simp) y).hasDerivAt).const_mul (Real.sin (Real.pi * x))
  apply Prod.ext
  · change Real.cos (Real.pi * x) * (Real.pi * u y) =
      deriv (fun z ↦ Real.sin (Real.pi * z) * u y) x
    rw [hx.deriv]
    simp only [id, mul_one]
    ring
  · exact hy.deriv.symm

theorem residual_coclosed (x y : ℝ) : codifferential residual x y = 0 := by
  have hx := (((Real.hasDerivAt_cos (Real.pi * x)).comp x
    ((hasDerivAt_id x).const_mul Real.pi)).mul_const (deriv v y / Real.pi)).neg
  have hy := (((v_smooth.differentiable (by simp) y).hasDerivAt).const_mul
    (Real.sin (Real.pi * x))).neg
  rw [codifferential_eq_coordinateDivergence]
  change -(y^2 * (deriv (fun z ↦ -(Real.cos (Real.pi * z) * (deriv v y / Real.pi))) x +
    deriv (fun z ↦ -(Real.sin (Real.pi * x) * v z)) y)) = 0
  rw [hx.deriv, hy.deriv]
  simp only [id, mul_one]
  field_simp [Real.pi_ne_zero] <;> ring

private theorem low_cutoff {y : ℝ} (hy : y < 5) :
    cutoff =ᶠ[𝓝 y] (fun _ ↦ 0) := by
  filter_upwards [gt_mem_nhds hy] with z hz
  exact Real.smoothTransition.zero_of_nonpos (by have h : z < 5 := hz; linarith)

private theorem high_cutoff {y : ℝ} (hy : 11/2 < y) :
    cutoff =ᶠ[𝓝 y] (fun _ ↦ 1) := by
  filter_upwards [lt_mem_nhds hy] with z hz
  exact Real.smoothTransition.one_of_one_le (by have h : 11/2 < z := hz; linarith)

theorem zero_below_cusp_band (x y : ℝ) (hy : y < 5) :
    potential x y = 0 ∧ residual x y = (0, 0) ∧ inputForm x y = (0, 0) := by
  have h := low_cutoff hy
  have hu : u =ᶠ[𝓝 y] (fun _ ↦ 0) := by
    filter_upwards [h] with z hz
    simp [u, hz]
  have hv : v =ᶠ[𝓝 y] (fun _ ↦ 0) := by
    filter_upwards [h] with z hz
    simp [v, hz]
  have hU : u y = 0 := hu.eq_of_nhds
  have hV : v y = 0 := hv.eq_of_nhds
  have hdU : deriv u y = 0 := by simpa using hu.deriv_eq
  have hdV : deriv v y = 0 := by simpa using hv.deriv_eq
  simp [potential, residual, inputForm, gradient, hU, hV, hdU, hdV]

theorem zero_input_near_boundary (x y : ℝ) (hy : 11/2 < y) :
    inputForm x y = (0, 0) := by
  have h := high_cutoff hy
  have hu : u =ᶠ[𝓝 y] s := by
    filter_upwards [h] with z hz
    simp [u, hz]
  have hv : v =ᶠ[𝓝 y] c := by
    filter_upwards [h] with z hz
    simp [v, hz]
  have hU : u y = s y := hu.eq_of_nhds
  have hV : v y = c y := hv.eq_of_nhds
  have hdU : deriv u y = c y := hu.deriv_eq.trans (s_deriv y).deriv
  have hdV : deriv v y = Real.pi ^ 2 * s y := hv.deriv_eq.trans (c_deriv y).deriv
  apply Prod.ext
  · change Real.cos (Real.pi * x) * (Real.pi * u y) +
      -(Real.cos (Real.pi * x) * (deriv v y / Real.pi)) = 0
    rw [hU, hdV]
    field_simp [Real.pi_ne_zero] <;> ring
  · simp [inputForm, gradient, residual, hdU, hV]

theorem potential_zero_on_boundary (x : ℝ) : potential x 6 = 0 := by
  simp [potential, u, s, t]

theorem correction_eq_residual (x y : ℝ) :
    ((inputForm x y).1 - partialX potential x y,
      (inputForm x y).2 - partialY potential x y) = residual x y := by
  have h := gradient_eq_partials x y
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  · change (gradient x y).1 + (residual x y).1 - partialX potential x y = _
    rw [hx]
    ring
  · change (gradient x y).2 + (residual x y).2 - partialY potential x y = _
    rw [hy]
    ring

theorem residual_nonzero_on_boundary : (residual (1/2) 6).2 = -1 := by
  have hc : cutoff 6 = 1 := (high_cutoff (y := 6) (by norm_num)).eq_of_nhds
  change -(Real.sin (Real.pi * (1/2)) * v 6) = -1
  rw [show Real.pi * (1/2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp [v, hc, c, t]

theorem chart_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ potential p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ residual p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ inputForm p.1 p.2) := by
  have hu : ContDiff ℝ ∞ (deriv u) := ContDiff.deriv' (by simpa using u_smooth)
  have hv : ContDiff ℝ ∞ (deriv v) := ContDiff.deriv' (by simpa using v_smooth)
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sin (Real.pi * p.1)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ Real.cos (Real.pi * p.1)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst)
  have hU := u_smooth.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have hV := v_smooth.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have hDU := hu.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have hDV := hv.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  exact ⟨hs.mul hU, ((hc.mul (hDV.div_const _)).neg).prodMk ((hs.mul hV).neg),
    ((hc.mul (contDiff_const.mul hU)).add (hc.mul (hDV.div_const _)).neg).prodMk
      ((hs.mul hDU).add (hs.mul hV).neg)⟩

theorem periodic (x y : ℝ) (m : ℤ) :
    potential (x + 2*m) y = potential x y ∧
    residual (x + 2*m) y = residual x y ∧ inputForm (x + 2*m) y = inputForm x y := by
  have h : Real.pi * (x + 2*m) = Real.pi*x + m*(2*Real.pi) := by ring
  simp only [potential, residual, inputForm, gradient, h,
    Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi, and_self]

end
end ManuscriptAudit.Paper10CoulombDirichletMode

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombDirichletMode.u_smooth,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.v_smooth,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.gradient_eq_partials,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.residual_coclosed,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.zero_below_cusp_band,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.zero_input_near_boundary,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.potential_zero_on_boundary,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.correction_eq_residual,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.residual_nonzero_on_boundary,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.chart_smooth,
      ``ManuscriptAudit.Paper10CoulombDirichletMode.periodic] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
