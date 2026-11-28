import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import PrimalitySheafVerification.ManuscriptAudit.Paper8BoundaryLaplaceHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossDirichletLaplace

/-! A pole of the continuation of the actual shifted Dirichlet series obstructs the ordered cutoff. -/

namespace ManuscriptAudit.Paper8OddCrossContinuationPole

open Filter Set
open Paper8BoundaryLaplaceHolomorphic Paper8OddCrossAbelObstruction
open Paper8OddCrossDirichletLaplace Paper8OddCrossZetaFactorization
open scoped Topology

noncomputable section

def crossShiftedDirichletSeries (w : ℂ) : ℂ := ∑' j, oddCrossZetaTerm ((w + 1) / 2) j

theorem crossAbelShiftedZeta_analyticOnNhd_of_ordered_limit {L : ℂ}
    (hL : Tendsto orderedCrossCutoff atTop (𝓝 L)) :
    AnalyticOnNhd ℂ crossAbelShiftedZeta {w : ℂ | 0 < w.re} := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1
    (Metric.isBounded_range_of_tendsto orderedCrossCutoff hL)
  have hB (t : ℝ) (_ : 0 < t) : ‖crossLogarithmicStep t‖ ≤ C := by
    have h := Metric.mem_ball.1 (hC (show crossLogarithmicStep t ∈ Set.range orderedCrossCutoff from ⟨_, rfl⟩))
    simpa only [dist_zero_right] using h.le
  have hA := differentiableOn_boundaryLaplace crossLogarithmicStep crossLogarithmicStep_measurable hB
  have hp : Differentiable ℂ (fun w : ℂ => (2 : ℂ) ^ (-(w + 1))) := by
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact Complex.differentiable_exp.comp (differentiable_const.mul
      (differentiable_id.add differentiable_const).neg)
  have hOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hDiff : DifferentiableOn ℂ crossAbelShiftedZeta {w : ℂ | 0 < w.re} :=
    ((hp.mul differentiable_id).differentiableOn).mul hA
  exact hDiff.analyticOnNhd hOpen

theorem cross_continuation_agrees_with_abel_of_ordered_limit {L : ℂ}
    (hL : Tendsto orderedCrossCutoff atTop (𝓝 L)) {P : ℂ → ℂ} {U : Set ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hU : IsPreconnected U) (hRight : U ⊆ {w : ℂ | 0 < w.re})
    {w₀ : ℂ} (h₀ : w₀ ∈ U) (h₁ : 1 < w₀.re)
    (hInitial : EqOn P crossShiftedDirichletSeries {w : ℂ | 1 < w.re}) :
    EqOn P crossAbelShiftedZeta U := by
  have hA := (crossAbelShiftedZeta_analyticOnNhd_of_ordered_limit hL).mono hRight
  have hOpen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hAgree : P =ᶠ[𝓝 w₀] crossAbelShiftedZeta := by
    filter_upwards [hOpen.mem_nhds h₁] with w hw
    exact (hInitial hw).trans (crossAbelShiftedZeta_eq_oddCrossZeta hw).symm
  exact hP.eqOn_of_preconnected_of_eventuallyEq hA hU h₀ hAgree

theorem no_ordered_cross_limit_of_continuation_residue {P : ℂ → ℂ} {U : Set ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hU : IsPreconnected U) (hRight : U ⊆ {w : ℂ | 0 < w.re})
    {w₀ : ℂ} (h₀ : w₀ ∈ U) (h₁ : 1 < w₀.re)
    (hInitial : EqOn P crossShiftedDirichletSeries {w : ℂ | 1 < w.re})
    {τ : ℝ} (hτ : τ ≠ 0)
    (hApproach : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) + (τ : ℂ) * Complex.I ∈ U)
    {r : ℂ} (hr : r ≠ 0)
    (hPole : Tendsto (fun ε : ℝ => (ε : ℂ) * P ((ε : ℂ) + (τ : ℂ) * Complex.I))
        (𝓝[>] 0) (𝓝 r)) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hA := cross_continuation_agrees_with_abel_of_ordered_limit hL hP hU hRight h₀ h₁ hInitial
  have hLimit := ordered_cross_cutoff_forces_zero_abel_residue hL hτ
  have hEq : (fun ε : ℝ => (ε : ℂ) * P ((ε : ℂ) + (τ : ℂ) * Complex.I)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => (ε : ℂ) * crossAbelShiftedZeta ((ε : ℂ) + (τ : ℂ) * Complex.I) := by
    filter_upwards [hApproach] with ε hε
    rw [hA hε]
  exact hr (tendsto_nhds_unique (hPole.congr' hEq) hLimit)

private theorem radial_tendsto (c : ℂ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) + c) (𝓝[>] 0) (𝓝[≠] c) := by
  have h : Continuous (fun ε : ℝ => (ε : ℂ) + c) := Complex.continuous_ofReal.add continuous_const
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [Complex.ofReal_zero, zero_add] using h.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)] with ε hε
    change (ε : ℂ) + c ≠ c
    exact fun hEq => (Complex.ofReal_ne_zero.mpr hε.ne') (add_right_cancel (hEq.trans (zero_add c).symm))

theorem radial_simple_pole_has_nonzero_residue {P : ℂ → ℂ} {c : ℂ}
    (hP : MeromorphicAt P c) (hOrder : meromorphicOrderAt P c = (-1 : ℤ)) :
    ∃ r : ℂ, r ≠ 0 ∧ Tendsto (fun ε : ℝ => (ε : ℂ) * P ((ε : ℂ) + c)) (𝓝[>] 0) (𝓝 r) := by
  obtain ⟨g, hg, hg₀, hEq⟩ := (meromorphicOrderAt_eq_int_iff hP).1 hOrder
  refine ⟨g c, hg₀, ?_⟩
  have hRad := radial_tendsto c
  refine (hg.continuousAt.tendsto.comp (hRad.mono_right nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [hRad.eventually hEq, (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)] with ε he hε
  change P ((ε : ℂ) + c) = ((ε : ℂ) + c - c) ^ (-1 : ℤ) • g ((ε : ℂ) + c) at he
  rw [he, add_sub_cancel_right, zpow_neg_one, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'), one_mul]

theorem no_ordered_cross_limit_of_continuation_simple_pole {P : ℂ → ℂ} {U : Set ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hU : IsPreconnected U) (hRight : U ⊆ {w : ℂ | 0 < w.re})
    {w₀ : ℂ} (h₀ : w₀ ∈ U) (h₁ : 1 < w₀.re)
    (hInitial : EqOn P crossShiftedDirichletSeries {w : ℂ | 1 < w.re})
    {τ : ℝ} (hτ : τ ≠ 0)
    (hApproach : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) + (τ : ℂ) * Complex.I ∈ U)
    (hM : MeromorphicAt P ((τ : ℂ) * Complex.I))
    (hOrder : meromorphicOrderAt P ((τ : ℂ) * Complex.I) = (-1 : ℤ)) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) := by
  obtain ⟨r, hr, hPole⟩ := radial_simple_pole_has_nonzero_residue hM hOrder
  exact no_ordered_cross_limit_of_continuation_residue hP hU hRight h₀ h₁ hInitial hτ hApproach hr hPole

end
end ManuscriptAudit.Paper8OddCrossContinuationPole

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossContinuationPole.cross_continuation_agrees_with_abel_of_ordered_limit,
      ``ManuscriptAudit.Paper8OddCrossContinuationPole.no_ordered_cross_limit_of_continuation_simple_pole] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
