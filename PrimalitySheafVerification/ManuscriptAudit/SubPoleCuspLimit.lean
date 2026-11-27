import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Periodic
import PrimalitySheafVerification.ManuscriptAudit.SubPoleGrowthRemovable

/-! A periodic holomorphic upper-half-plane function with sub-pole q-growth has a finite cusp limit. -/

namespace ManuscriptAudit.SubPoleCuspLimit

open Set Filter Function Function.Periodic
open SubPoleGrowthRemovable
open scoped Topology

theorem exists_limit_of_subPole_cuspGrowth {f : ℂ → ℂ} {width C exponent : ℝ}
    (hWidth : 0 < width) (hPer : Periodic f width) (hExp : exponent < 1)
    (hHol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ f z)
    (hBound : ∀ᶠ z in comap Complex.im atTop,
        ‖f z‖ ≤ C / ‖qParam width z‖ ^ exponent) :
    ∃ L : ℂ, Tendsto f (comap Complex.im atTop) (𝓝 L) := by
  let qFunction := cuspFunction width f
  have hQHol : ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ qFunction q :=
    eventually_differentiableAt_cuspFunction_nhds_ne_zero hWidth hPer hHol
  have hQBound : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖qFunction q‖ ≤ C / ‖q‖ ^ exponent := by
    filter_upwards [(invQParam_tendsto hWidth).eventually hBound, self_mem_nhdsWithin] with q hq hq0
    have hn : q ≠ 0 := by simpa using hq0
    rw [qParam_right_inv hWidth.ne' hn] at hq
    simpa only [qFunction, cuspFunction_eq_of_nonzero _ _ hn] using hq
  have hQSmall := isLittleO_sub_inverse_of_mul_tendsto_zero
    (tendsto_mul_zero_of_subPoleGrowth hExp hQBound)
  have hQLimit := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
    hQHol hQSmall
  refine ⟨_, ?_⟩
  simpa only [Function.comp_def, qFunction, eq_cuspFunction hWidth.ne' hPer] using
    hQLimit.comp (qParam_tendsto hWidth)

end ManuscriptAudit.SubPoleCuspLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.SubPoleCuspLimit.exists_limit_of_subPole_cuspGrowth
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
