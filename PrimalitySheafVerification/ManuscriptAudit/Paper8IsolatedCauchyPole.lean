import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Order

/-! An isolated nonzero coefficient of an absolutely summable Cauchy transform gives a simple pole. -/

namespace ManuscriptAudit.Paper8IsolatedCauchyPole

open Filter Set
open scoped Topology

noncomputable section

def cauchySpectralSeries {I : Type*} (w a : I → ℂ) (z : ℂ) : ℂ :=
  ∑' i, a i / (z - w i)

theorem cauchySpectralSeries_simple_pole {I : Type*} (w a : I → ℂ)
    (hSum : Summable (fun i => ‖a i‖)) (i₀ : I) (hA : a i₀ ≠ 0)
    {r : ℝ} (hr : 0 < r) (hIso : ∀ i, i ≠ i₀ → r ≤ ‖w i - w i₀‖) :
    MeromorphicAt (cauchySpectralSeries w a) (w i₀) ∧
      meromorphicOrderAt (cauchySpectralSeries w a) (w i₀) = (-1 : ℤ) := by
  classical
  let U := Metric.ball (w i₀) (r / 2)
  let f (i : I) (z : ℂ) := if i = i₀ then 0 else a i / (z - w i)
  let F (z : ℂ) := ∑' i, f i z
  have hr' : 0 < r / 2 := half_pos hr
  have hRel (i : I) (hi : i ≠ i₀) (z : ℂ) (hz : z ∈ U) : r / 2 ≤ ‖z - w i‖ := by
    have hZ : ‖z - w i₀‖ < r / 2 := by simpa only [U, Metric.mem_ball, dist_eq_norm] using hz
    have hTriangle : ‖w i - w i₀‖ ≤ ‖z - w i‖ + ‖z - w i₀‖ := by
      calc
        _ = ‖(w i - z) + (z - w i₀)‖ := by congr 1; ring
        _ ≤ ‖w i - z‖ + ‖z - w i₀‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev (w i) z]
    linarith [hIso i hi]
  have hBound (i : I) (z : ℂ) (hz : z ∈ U) : ‖f i z‖ ≤ (r / 2)⁻¹ * ‖a i‖ := by
    by_cases hi : i = i₀
    · rw [f, if_pos hi, norm_zero]
      positivity
    · rw [f, if_neg hi, norm_div]
      have h := div_le_div_of_nonneg_left (norm_nonneg (a i)) hr' (hRel i hi z hz)
      simpa only [div_eq_mul_inv, mul_comm] using h
  have hDiff (i : I) : DifferentiableOn ℂ (f i) U := by
    by_cases hi : i = i₀
    · simp only [f, if_pos hi]
      exact differentiableOn_const
    · simp only [f, if_neg hi]
      exact differentiableOn_const.div (differentiableOn_id.sub differentiableOn_const)
        (fun z hz => norm_pos_iff.mp (hr'.trans_le (hRel i hi z hz)))
  have hMajorant : Summable (fun i => (r / 2)⁻¹ * ‖a i‖) := hSum.mul_left _
  have hFD : DifferentiableOn ℂ F U :=
    Complex.differentiableOn_tsum_of_summable_norm hMajorant hDiff Metric.isOpen_ball hBound
  have hFA : AnalyticAt ℂ F (w i₀) :=
    (hFD.analyticOnNhd Metric.isOpen_ball) _ (Metric.mem_ball_self hr')
  let G (z : ℂ) := a i₀ + (z - w i₀) * F z
  have hGA : AnalyticAt ℂ G (w i₀) :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hFA)
  have hG₀ : G (w i₀) ≠ 0 := by simpa only [G, sub_self, zero_mul, add_zero] using hA
  have hSplit (z : ℂ) (hz : z ∈ U) :
      cauchySpectralSeries w a z = a i₀ / (z - w i₀) + F z := by
    have hFS : Summable (fun i => f i z) := hMajorant.of_norm_bounded (fun i => hBound i z hz)
    have hOne := hasSum_ite_eq i₀ (a i₀ / (z - w i₀))
    have hBoth := hOne.add hFS.hasSum
    have hFull : HasSum (fun i => a i / (z - w i)) (a i₀ / (z - w i₀) + F z) := by
      refine hBoth.congr_fun fun i => ?_
      by_cases hi : i = i₀
      · subst i
        simp [f]
      · simp [f, hi]
    exact hFull.tsum_eq
  have hEq : ∀ᶠ z in 𝓝[≠] (w i₀), cauchySpectralSeries w a z = (z - w i₀) ^ (-1 : ℤ) • G z := by
    filter_upwards [(Metric.ball_mem_nhds _ hr').filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : ∀ᶠ z : ℂ in 𝓝[≠] (w i₀), z ≠ w i₀)] with z hz hn
    rw [hSplit z hz, zpow_neg_one, smul_eq_mul, G]
    field_simp [sub_ne_zero.mpr hn] <;> ring
  have hM : MeromorphicAt (cauchySpectralSeries w a) (w i₀) :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.2 ⟨-1, G, hGA, hEq⟩
  exact ⟨hM, (meromorphicOrderAt_eq_int_iff hM).2 ⟨G, hGA, hG₀, hEq⟩⟩

end
end ManuscriptAudit.Paper8IsolatedCauchyPole

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8IsolatedCauchyPole.cauchySpectralSeries_simple_pole
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
