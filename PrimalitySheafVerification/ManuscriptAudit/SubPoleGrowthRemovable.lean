import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A holomorphic cusp quotient whose growth exponent is below one extends at the cusp. -/

namespace ManuscriptAudit.SubPoleGrowthRemovable

open Set Filter Function Asymptotics
open scoped Topology

theorem tendsto_mul_zero_of_subPoleGrowth {g : ℂ → ℂ} {C exponent : ℝ}
    (hExp : exponent < 1)
    (hBound : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖g q‖ ≤ C / ‖q‖ ^ exponent) :
    Tendsto (fun q => q * g q) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hNorm : Tendsto (fun q : ℂ => ‖q‖) (𝓝[≠] 0) (𝓝 0) := by
    have h := (continuous_norm.continuousAt : ContinuousAt (fun q : ℂ => ‖q‖) 0).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have hMajor : Tendsto (fun q : ℂ => C * ‖q‖ ^ (1 - exponent)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hNorm.rpow_const_nhds_zero (sub_pos.mpr hExp)).const_mul C
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hMajor
  filter_upwards [hBound, self_mem_nhdsWithin] with q hq hq0
  have hNonzero : q ≠ 0 := by simpa using hq0
  rw [norm_mul]
  calc
    ‖q‖ * ‖g q‖ ≤ ‖q‖ * (C / ‖q‖ ^ exponent) :=
      mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    _ = C * ‖q‖ ^ (1 - exponent) := by
      rw [Real.rpow_sub (norm_pos_iff.mpr hNonzero), Real.rpow_one]
      ring

theorem removable_of_mul_tendsto_zero {g : ℂ → ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 0)
    (hg : DifferentiableOn ℂ g (s \ {0}))
    (h : Tendsto (fun q => q * g q) (𝓝[≠] (0 : ℂ)) (𝓝 0)) :
    ∃ extension : ℂ → ℂ, (s \ {0}).EqOn extension g ∧ DifferentiableOn ℂ extension s := by
  have hOne : Tendsto (fun q : ℂ => q) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hSecond : Tendsto (fun q : ℂ => q * g 0) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_mul] using hOne.mul_const (g 0)
  have hDiff : Tendsto (fun q : ℂ => q * g q - q * g 0) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [sub_zero] using h.sub hSecond
  have hLittle : (fun q : ℂ => g q - g 0) =o[𝓝[≠] (0 : ℂ)] (fun q => (q - 0)⁻¹) := by
    apply isLittleO_of_tendsto'
    · filter_upwards [self_mem_nhdsWithin] with q hq
      have hq0 : q ≠ 0 := by simpa using hq
      simp [hq0]
    · exact hDiff.congr (fun q => by simp [div_eq_mul_inv, sub_mul, mul_comm])
  refine ⟨Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g), ?_,
    Complex.differentiableOn_update_limUnder_of_isLittleO hs hg hLittle⟩
  intro q hq
  have hq0 : q ≠ 0 := by simpa using hq.2
  exact Function.update_of_ne hq0 _ _

theorem removable_of_subPoleGrowth {g : ℂ → ℂ} {s : Set ℂ} {C exponent : ℝ}
    (hs : s ∈ 𝓝 0) (hg : DifferentiableOn ℂ g (s \ {0})) (hExp : exponent < 1)
    (hBound : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖g q‖ ≤ C / ‖q‖ ^ exponent) :
    ∃ extension : ℂ → ℂ, (s \ {0}).EqOn extension g ∧ DifferentiableOn ℂ extension s :=
  removable_of_mul_tendsto_zero hs hg (tendsto_mul_zero_of_subPoleGrowth hExp hBound)

end ManuscriptAudit.SubPoleGrowthRemovable

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SubPoleGrowthRemovable.tendsto_mul_zero_of_subPoleGrowth,
      ``ManuscriptAudit.SubPoleGrowthRemovable.removable_of_mul_tendsto_zero,
      ``ManuscriptAudit.SubPoleGrowthRemovable.removable_of_subPoleGrowth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
